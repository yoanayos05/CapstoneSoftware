#!/usr/bin/env python3
"""Resumable GitHub REST closure/merge collector. Python 3.10+, pip install requests.

Run: python3 collect_codex_closures.py
Token: GITHUB_TOKEN environment variable, or hidden prompt.
Resume: repeat the command with the same --out directory.
Recovery: --refresh 2026-09-01T00:00:00Z 2026-10-01T00:00:00Z

Scope: unique currently merged PRs, currently closed/unmerged PRs, and
currently closed issues, grouped by their recorded merged_at/closed_at.
This is NOT a historical timeline of every close/reopen event. Reopened items
and earlier closures overwritten by later closures cannot be reconstructed.
All authors/actors (including bots) are included. No creation-date restriction.
Weeks start Monday UTC. Boundary weeks/months are clipped to observation dates.
Search completeness is checked against API totals, not guaranteed historical
completeness: GitHub search is indexed, mutable, and is not an atomic snapshot.

Outputs: runs/<run-id>/{weekly.csv,monthly.csv,records.csv,manifest.json}.
latest_run.json points to latest attempt; latest_complete.json to latest complete
attempt. Old runs are never overwritten. Failed intervals produce blank counts
in affected bins, with *_observed columns holding partial observed counts.
Cache/checkpoint/log files live under --out. Do not run two copies on one folder.
"""
import argparse
import csv
import getpass
import hashlib
import io
import json
import os
from pathlib import Path
import random
import sys
import tempfile
import time
import uuid
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import urlencode, urlparse

import requests

UTC = timezone.utc
API = 'https://api.github.com'
VERSION = '1.0'
KINDS = {
    'merged_prs': ('is:pr is:merged', 'merged'),
    'closed_without_merge_prs': ('is:pr is:closed is:unmerged', 'closed'),
    'closed_issues': ('is:issue is:closed', 'closed'),
}


def dt(value):
    result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    if result.tzinfo is None or result.microsecond:
        raise ValueError('Use timezone-aware ISO dates with whole seconds, e.g. 2026-09-01T00:00:00Z')
    return result.astimezone(UTC)


def iso(value):
    return value.astimezone(UTC).strftime('%Y-%m-%dT%H:%M:%SZ')


def now():
    return iso(datetime.now(UTC))


def atomic(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix='.' + path.name, dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8', newline='') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def save(path, value):
    atomic(path, json.dumps(value, indent=2, sort_keys=True) + '\n')


def read(path):
    try:
        return json.loads(Path(path).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        return None


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


class Failure(Exception):
    pass


class Permanent(Failure):
    pass


class Split(Failure):
    pass


class Collector:
    def __init__(self, args, token):
        self.args = args
        self.root = Path(args.out)
        self.root.mkdir(parents=True, exist_ok=True)
        self.session = requests.Session()
        self.session.headers.update({'Authorization': 'Bearer ' + token,
            'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28',
            'User-Agent': 'codex-closure-research/1.0'})
        self.token = token
        previous = read(self.root / 'checkpoint.json') or {}
        self.not_before = previous.get('resume_after_epoch', 0) if isinstance(previous, dict) else 0
        self.last_request = 0
        self.context = {}
        self.completed = []
        self.gaps = []
        self.records = {}

    def log(self, message):
        message = str(message).replace(self.token, '[REDACTED]') if self.token else str(message)
        line = f'{now()} {message}'
        print(line, flush=True)
        with (self.root / 'collection.log').open('a', encoding='utf-8') as f:
            f.write(line + '\n')
            f.flush()

    def checkpoint(self, **extra):
        save(self.root / 'checkpoint.json', {'at': now(), **self.context, **extra})

    def wait(self, seconds, reason):
        seconds = max(0, seconds)
        self.checkpoint(reason=reason, resume_after_epoch=time.time() + seconds)
        self.log(f'{self.context.get("kind", "request")} waiting {seconds:.1f}s: {reason}')
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            time.sleep(min(30, max(0, deadline - time.monotonic())))

    def request(self, url, validator, force=False):
        parsed = urlparse(url)
        if parsed.scheme != 'https' or parsed.netloc != 'api.github.com' or parsed.username:
            raise Permanent('Refusing unexpected pagination URL origin')
        cache = self.root / 'cache' / (digest(url) + '.json')
        old = read(cache)
        if not force and isinstance(old, dict):
            try:
                if old['url'] == url and old['sha256'] == digest(old['body']) and validator(old['body']):
                    return old
            except (KeyError, TypeError, ValueError):
                pass
            self.log('Invalid cache entry; downloading again')
        for attempt in range(self.args.retries + 1):
            self.checkpoint(url=url, attempt=attempt)
            delay = max(self.not_before - time.time(), self.last_request + 2.1 - time.time())
            if delay > 0:
                self.wait(delay, 'request pacing / rate-limit headers')
            try:
                self.last_request = time.time()
                response = self.session.get(url, timeout=(15, 90), allow_redirects=False)
                headers = response.headers
                if headers.get('X-RateLimit-Remaining') == '0':
                    self.not_before = max(self.not_before, float(headers.get('X-RateLimit-Reset', time.time()+60)) + 2)
                try:
                    body = response.json()
                except ValueError:
                    body = None
                message = str(body.get('message', '')) if isinstance(body, dict) else ''
                limited = response.status_code == 429 or (response.status_code == 403 and (
                    headers.get('X-RateLimit-Remaining') == '0' or headers.get('Retry-After') or
                    'rate limit' in message.lower() or 'abuse' in message.lower()))
                if limited:
                    seconds = min(900, 60 * 2 ** attempt)
                    retry_after = headers.get('Retry-After')
                    if retry_after:
                        try:
                            seconds = max(seconds, float(retry_after))
                        except ValueError:
                            seconds = max(seconds, parsedate_to_datetime(retry_after).timestamp() - time.time())
                    seconds = max(seconds, self.not_before - time.time())
                    reason = f'HTTP {response.status_code} rate limit'
                elif response.status_code in (500, 502, 503, 504):
                    seconds, reason = min(120, 2 ** (attempt+1)), f'HTTP {response.status_code} temporary server failure'
                elif response.status_code != 200:
                    labels = {401: 'authentication failed; check GITHUB_TOKEN',
                              403: 'permission denied (not a rate limit)',
                              404: 'repository/resource missing or inaccessible',
                              422: 'invalid query or request; inspect query in checkpoint'}
                    raise Permanent(f'HTTP {response.status_code}: {labels.get(response.status_code, "unexpected status")}; {message[:300]}')
                elif body is None or not validator(body):
                    seconds, reason = min(120, 2 ** (attempt+1)), 'invalid JSON or unexpected response schema'
                else:
                    envelope = {'url': url, 'retrieved_at': now(), 'body': body,
                                'sha256': digest(body), 'next': response.links.get('next', {}).get('url'),
                                'headers': {k: headers.get(k) for k in ('X-GitHub-Request-Id',
                                'X-RateLimit-Remaining', 'X-RateLimit-Reset', 'ETag')}}
                    save(cache, envelope)
                    self.checkpoint(url=url, cached=True)
                    return envelope
            except requests.exceptions.RequestException as exc:
                # Avoid printing request headers or exception contents containing credentials.
                seconds, reason = min(120, 2 ** (attempt+1)), f'temporary transport error ({type(exc).__name__})'
            if attempt == self.args.retries:
                raise Failure(f'{reason}; retry budget exhausted ({self.args.retries} retries)')
            self.wait(seconds + random.uniform(0.1, 1.5), reason + f'; retry {attempt+1}/{self.args.retries}')
        raise Failure('Request did not complete')

    def interval(self, kind, start, end, force=False):
        qualifiers, field = KINDS[kind]
        # GitHub search ranges are inclusive; timestamps have second precision.
        query = f'repo:{self.args.repo} {qualifiers} {field}:{iso(start)}..{iso(end-timedelta(seconds=1))}'
        self.context = {'kind': kind, 'start': iso(start), 'end_exclusive': iso(end), 'query': query}
        url = API + '/search/issues?' + urlencode({'q': query, 'per_page': 100, 'sort': 'created', 'order': 'asc'})
        urls, fingerprints, items = set(), set(), {}
        expected = None
        page = 0
        retrieved = []
        try:
            while url:
                if url in urls:
                    raise Split('Repeated next-page URL')
                urls.add(url)
                page += 1
                self.context['page'] = page
                env = self.request(url, lambda b: isinstance(b, dict) and isinstance(b.get('items'), list)
                    and isinstance(b.get('total_count'), int) and isinstance(b.get('incomplete_results'), bool)
                    and all(isinstance(x, dict) and isinstance(x.get('id'), int) for x in b['items']), force)
                body = env['body']
                retrieved.append(env['retrieved_at'])
                if body['incomplete_results'] or body['total_count'] > 1000:
                    raise Split('Search incomplete or exceeds 1,000-result cap')
                if expected is None:
                    expected = body['total_count']
                if expected != body['total_count']:
                    raise Split('Search total changed between pages')
                fingerprint = tuple(sorted(x['id'] for x in body['items']))
                if fingerprint and fingerprint in fingerprints:
                    raise Split('Repeated page contents')
                fingerprints.add(fingerprint)
                for item in body['items']:
                    items[item['id']] = item
                self.log(f'{kind} [{iso(start)}, {iso(end)}) page {page}; downloaded unique records={len(items)}/{expected}')
                url = env.get('next')
            if len(items) != expected:
                raise Split(f'Count mismatch: unique={len(items)}, total={expected}')
            records = []
            for item in items.values():
                is_pr = 'pull_request' in item
                if is_pr != (kind != 'closed_issues'):
                    raise Split('Unexpected item type in search result')
                stamp = item.get('closed_at')
                if kind == 'merged_prs':
                    stamp = item['pull_request'].get('merged_at')
                    if not stamp:
                        detail = self.request(f'{API}/repos/{self.args.repo}/pulls/{item["number"]}',
                            lambda b: isinstance(b, dict) and 'merged_at' in b and 'number' in b, force)
                        stamp = detail['body']['merged_at']
                if not stamp or not start <= dt(stamp) < end:
                    raise Split('Missing/out-of-interval timestamp; search index or record changed')
                user = item.get('user') or {}
                records.append({'activity_type': kind, 'id': item['id'], 'number': item['number'],
                    'event_at': stamp, 'url': item['html_url'], 'author': user.get('login', ''),
                    'author_type': user.get('type', ''), 'created_at': item.get('created_at'),
                    'updated_at': item.get('updated_at')})
            for record in records:
                self.records[(kind, record['id'])] = record
            self.completed.append({**self.context, 'count': len(records), 'api_total': expected,
                                   'page_retrieval_times': retrieved})
            self.checkpoint(status='interval_complete', count=len(records))
            self.log(f'COMPLETED {kind} [{iso(start)}, {iso(end)}): {len(records)}')
        except Split as exc:
            seconds = int((end-start).total_seconds())
            if seconds <= 1:
                raise Failure(f'Cannot split below one second: {exc}') from exc
            mid = start + timedelta(seconds=seconds//2)
            self.log(f'SPLITTING {kind} [{iso(start)}, {iso(end)}): {exc}')
            # Fresh child queries avoid repeating stale/inconsistent cached pagination.
            self.collect(kind, start, mid, True)
            self.collect(kind, mid, end, True)

    def collect(self, kind, start, end, force=False):
        try:
            self.interval(kind, start, end, force)
        except Permanent:
            raise
        except (Failure, ValueError, KeyError, TypeError) as exc:
            gap = {'kind': kind, 'start': iso(start), 'end_exclusive': iso(end), 'reason': str(exc)}
            self.gaps.append(gap)
            self.checkpoint(status='gap', gap=gap)
            self.log(f'UNRESOLVED GAP {gap}')


def bins(start, end, monthly):
    cursor = start.replace(day=1) if monthly else start - timedelta(days=start.weekday())
    cursor = cursor.replace(hour=0, minute=0, second=0)
    while cursor < end:
        following = (cursor.replace(year=cursor.year+1, month=1) if cursor.month == 12
                     else cursor.replace(month=cursor.month+1)) if monthly else cursor + timedelta(days=7)
        yield cursor, max(cursor, start), min(following, end), following
        cursor = following


def csv_text(rows, fields):
    stream = io.StringIO(newline='')
    writer = csv.DictWriter(stream, fieldnames=fields)
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def aggregates(records, completed, start, end, monthly):
    output = []
    for label, lo, hi, full_hi in bins(start, end, monthly):
        row = {'period_start': iso(label), 'observed_start': iso(lo), 'observed_end_exclusive': iso(hi),
               'partial_calendar_period': lo != label or hi != full_hi}
        for kind in KINDS:
            count = sum(r['activity_type'] == kind and lo <= dt(r['event_at']) < hi for r in records)
            spans = sorted((max(lo, dt(c['start'])), min(hi, dt(c['end_exclusive'])))
                           for c in completed if c['kind'] == kind
                           and dt(c['start']) < hi and dt(c['end_exclusive']) > lo)
            cursor = lo
            for a, b in spans:
                if a > cursor:
                    break
                cursor = max(cursor, b)
            valid = cursor >= hi
            row[kind] = count if valid else ''
            row[kind + '_observed'] = count
            row[kind + '_complete'] = valid
        output.append(row)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--repo', default='openai/codex')
    parser.add_argument('--start', default='2025-10-22T00:00:00Z')
    parser.add_argument('--end', default='2026-10-21T00:00:00Z')
    parser.add_argument('--out', default='codex_closure_data')
    parser.add_argument('--retries', type=int, default=8)
    parser.add_argument('--refresh', nargs=2, action='append', default=[], metavar=('START', 'END'),
                        help='Bypass cache in overlapping weekly collection intervals; repeatable')
    args = parser.parse_args()
    try:
        start, end = dt(args.start), dt(args.end)
        refresh = [(dt(a), dt(b)) for a, b in args.refresh]
        if start >= end or args.retries < 0 or any(a >= b for a, b in refresh):
            raise ValueError('Start must precede end; retries must be nonnegative')
        if len(args.repo.split('/')) != 2 or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_./' for c in args.repo):
            raise ValueError('Repository must be owner/name')
    except ValueError as exc:
        parser.error(str(exc))
    root = Path(args.out)
    root.mkdir(parents=True, exist_ok=True)
    # Advisory lock automatically releases on crashes (macOS/Linux/Windows).
    lock = (root / '.lock').open('a+b')
    try:
        if os.name == 'nt':
            import msvcrt
            lock.seek(0); lock.write(b'0'); lock.flush(); lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        parser.error('Another collector is using this output directory')
    scope = {'version': VERSION, 'repo': args.repo, 'start': iso(start), 'end_exclusive': iso(end)}
    scope_path = root / 'scope.json'
    if scope_path.exists() and read(scope_path) != scope:
        parser.error('Existing output scope differs or is damaged; use another --out directory')
    save(scope_path, scope)
    token = os.environ.get() or getpass.getpass('GitHub token (hidden): ')
    if not token.strip():
        parser.error('A GitHub token is required')
    collector = Collector(args, token.strip())
    begun = now()
    stopped = None
    try:
        for kind in KINDS:
            cursor = start
            while cursor < end:
                following = min(cursor + timedelta(days=7), end)
                force = any(a < following and b > cursor for a, b in refresh)
                collector.collect(kind, cursor, following, force)
                cursor = following
    except (Permanent, KeyboardInterrupt) as exc:
        stopped = 'Interrupted by user' if isinstance(exc, KeyboardInterrupt) else str(exc)
        collector.log(f'STOPPED: {stopped}; resume with the same command')
    records = sorted(collector.records.values(), key=lambda r: (r['event_at'], r['activity_type'], r['id']))
    weekly = aggregates(records, collector.completed, start, end, False)
    monthly = aggregates(records, collector.completed, start, end, True)
    complete = not stopped and all(row[k+'_complete'] for row in weekly for k in KINDS)
    run_id = datetime.now(UTC).strftime('%Y%m%dT%H%M%S') + '-' + uuid.uuid4().hex[:8]
    dest = root / 'runs' / run_id
    fields = ['activity_type', 'id', 'number', 'event_at', 'url', 'author', 'author_type', 'created_at', 'updated_at']
    atomic(dest / 'records.csv', csv_text(records, fields))
    for filename, rows in [('weekly.csv', weekly), ('monthly.csv', monthly)]:
        atomic(dest / filename, csv_text(rows, list(rows[0])))
    manifest = {**scope, 'run_id': run_id, 'started_at': begun, 'finished_at': now(),
        'complete_for_query_scope': complete, 'stopped_reason': stopped, 'completed_intervals': collector.completed,
        'unresolved_gaps': collector.gaps, 'refresh_ranges': args.refresh, 'retries': args.retries,
        'record_count': len(records), 'totals': {k: sum(r['activity_type']==k for r in records) for k in KINDS},
        'scope_notes': __doc__, 'api_version': '2022-11-28', 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'incomplete_bins': [r['period_start'] for r in weekly if not all(r[k+'_complete'] for k in KINDS)]}
    save(dest / 'manifest.json', manifest)
    pointer = {'run_id': run_id, 'directory': str(dest.resolve()), 'complete_for_query_scope': complete}
    save(root / 'latest_run.json', pointer)
    if complete:
        save(root / 'latest_complete.json', pointer)
    collector.log(f'{"COMPLETE FOR DOCUMENTED QUERY SCOPE" if complete else "INCOMPLETE"}: {len(records)} records; outputs: {dest.resolve()}')
    return 0 if complete else 2


if __name__ == '__main__':
    sys.exit(main())
