#!/usr/bin/env python3
"""Resumable GitHub REST activity collector (Python 3.10+, requests).

INSTALL / RUN
  python3 -m pip install requests
  python3 collect_codex_activity.py
A token is read from GITHUB_TOKEN or GH_TOKEN, or requested with a hidden prompt.
Never put a token in this file or a command-line argument.

DEFAULT SCOPE
  openai/codex; [2025-10-22T00:00:00Z, 2026-10-21T00:00:00Z).
  This EXCLUDES the entire day 21 October 2026.
  Contribution = authored commit reachable from a pinned default-branch HEAD,
  issue opened, or PR opened. Count one per unique SHA/issue ID/PR ID, not lines
  changed. Reviews/comments/workflow runs are NOT counted as contributions.
  Commits use committer timestamp for inclusion, GitHub author for attribution;
  coauthors are not expanded. Unlinked authors have no invented GitHub ID.
  Account IDs identify accounts, not proven distinct people. Bot labels use API
  type Bot, login ending [bot], and optional manual overrides; 'other_user'
  does NOT certify a human. Missing identities remain 'unknown'.

RESPONSES
  Issues opened in the window only, excluding PRs. First non-author issue
  comment in each responder class (bot, other_user, unknown), before END.
  Also return first response overall. Comments/reactions by the author,
  reactions, labels, assignments, closures, and reviews are not responses.
  No response is blank/censored, NEVER zero hours. Unknown-author issues cannot
  reliably exclude self-replies and are marked identity_unresolved.
  Weekly/monthly response summaries group by ISSUE OPENING date, not reply date.
  Response means/medians cover observed replies only; report censored counts too.

ACTIONS
  Count workflow RUN IDs created in the window, separately for push and
  pull_request; current status/conclusion at EACH PAGE'S retrieval time.
  Latest run_attempt is recorded, but reruns are NOT counted as extra run IDs.
  A push run is not one commit. A single PR/push may trigger multiple workflows.
  REST workflow runs do not expose pull_request action=opened. ALL returned
  pull_request runs are labeled activity_action_unknown; NONE are asserted to
  be opening-only runs. pull_request_target is excluded. Historical states at
  the cutoff and deleted/inaccessible runs cannot be reconstructed by this API.

FILES (under --out, default codex_activity)
  cache.sqlite3: transactional page cache, query/fetch metadata, checkpoints,
    rate-limit waits, interval audit. Validated JSON + SHA256 checksum per page.
  progress.log: append-only progress, retries, completed intervals and gaps.
  exports/<unique timestamp>/ : protected snapshot, never overwrite old exports.
    contributors_all.csv / contributors_more_than_one.csv: full-period counts.
    contributor_period_counts.csv: each observed account's week/month counts
      and total; >1 within period is distinct from >1 over the full window.
    activity_period_counts.csv: repo activity counts + unique/repeat accounts.
    activities.csv: one row per contribution, with ID, UTC time, account label.
    issue_responses.csv: one row per issue AND responder class, plus any.
    response_period_summary.csv: issues, observed/unanswered counts, hours.
    workflow_runs.csv / workflow_period_counts.csv: raw & zero-filled aggregates.
    manifest.json: scope, definitions, retrieval range, completeness/gaps.
  latest.json: atomically updated pointer (previous version backed up).
  CSV week starts Monday UTC; months are calendar months; boundary bins partial.
  Unknown statuses/conclusions are retained. Null conclusions use 'none'.

RECOVERY
  Rerun the same command to replay valid cached pages and resume missing pages.
  python3 collect_codex_activity.py --refresh-start 2026-09-01T00:00:00Z \
      --refresh-end 2026-09-08T00:00:00Z
  Refresh bypasses cache for overlapping weekly collection intervals, not just
  those exact dates. It also refetches the repository comments scan (that API
  has no upper date bound). The rest is reused, then merged and deduplicated.
  --refresh-all retrieves a fresh snapshot (same pinned commit HEAD).
  --retry-failed refreshes intervals recorded as failed in a previous invocation.
  Use a NEW --out directory to pin a new HEAD or change scope. Do not run two
  collector processes against the same directory. Ctrl-C preserves cache.

LIMITATIONS
  API-visible inventory, not a guaranteed complete historical archive. Search
  indexes and mutable page lists can change during collection. Totals validate
  where available; list endpoints have no authoritative total. HTTP success
  alone is not counted as completeness. Exports with gaps exit 2 and explicitly
  say incomplete. Deleted data and account classification limitations remain
  even when all requests finish. Old cached statuses are not 'current today';
  --refresh-all updates them. SQLite must stay on a local disk, not a live-sync
  network folder. Cached response bodies may contain publicly posted text.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import csv
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
import getpass
import hashlib
import json
import logging
import os
from pathlib import Path
import random
import shutil
import sqlite3
import statistics
import sys
import tempfile
import time
from urllib.parse import urlencode, urlsplit, quote

import requests

UTC = timezone.utc
API = 'https://api.github.com'
VERSION = '2022-11-28'
LABELS = ('bot', 'other_user', 'unknown')
KINDS = ('commit', 'issue_opened', 'pr_opened')
STATUSES = ('queued', 'in_progress', 'completed', 'waiting', 'pending', 'requested')
CONCLUSIONS = ('success', 'failure', 'cancelled', 'timed_out', 'skipped',
               'action_required', 'stale', 'neutral', 'none')


def dt(value):
    result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    if result.tzinfo is None or result.microsecond:
        raise ValueError('Use timezone-aware whole-second timestamps, e.g. 2026-09-01T00:00:00Z')
    return result.astimezone(UTC)


def iso(value):
    return value.astimezone(UTC).isoformat(timespec='seconds').replace('+00:00', 'Z')


def now():
    return iso(datetime.now(UTC))


def dump(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':'))


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def atomic_json(path, data, backup=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name + '.')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            json.dump(data, stream, ensure_ascii=False, indent=2)
            stream.flush()
            os.fsync(stream.fileno())
        if backup and path.exists():
            shutil.copy2(path, path.with_name(path.name + '.' + str(time.time_ns()) + '.bak'))
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


class CollectionError(Exception):
    pass


class FatalAPI(CollectionError):
    pass


class SplitNeeded(CollectionError):
    pass


class Store:
    def __init__(self, path):
        self.db = sqlite3.connect(path)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.executescript('''
          CREATE TABLE IF NOT EXISTS pages (
            url TEXT PRIMARY KEY, payload TEXT NOT NULL, checksum TEXT NOT NULL,
            fetched TEXT NOT NULL, session TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS audit (
            timestamp TEXT, kind TEXT, start TEXT, end TEXT, status TEXT, detail TEXT);
        ''')
        self.db.commit()

    def get(self, key, default=None):
        row = self.db.execute('SELECT value FROM meta WHERE key=?', (key,)).fetchone()
        return json.loads(row[0]) if row else default

    def set(self, key, value):
        with self.db:
            self.db.execute('INSERT OR REPLACE INTO meta VALUES (?,?)', (key, dump(value)))

    def audit(self, kind, a, b, status, detail):
        with self.db:
            self.db.execute('INSERT INTO audit VALUES (?,?,?,?,?,?)',
                            (now(), kind, iso(a), iso(b), status, str(detail)))


class Client:
    def __init__(self, store, token, retries=8, delay=0.25):
        self.store, self.token, self.retries, self.delay = store, token, retries, delay
        self.session_id = str(time.time_ns())
        self.http = requests.Session()
        self.http.headers.update({'Accept': 'application/vnd.github+json',
                                  'X-GitHub-Api-Version': VERSION,
                                  'User-Agent': 'codex-academic-activity-collector/1.0',
                                  'Authorization': 'Bearer ' + token})
        self.used_pages = {}

    def safe(self, text):
        return str(text).replace(self.token, '[REDACTED]')[:500]

    def wait(self, seconds, reason, bucket):
        deadline = time.time() + max(0, seconds)
        self.store.set('wait:' + bucket, deadline)
        logging.warning('%s; waiting %.1f seconds (progress saved)', reason, seconds)
        while time.time() < deadline:
            time.sleep(min(30, max(0, deadline - time.time())))
        self.store.set('wait:' + bucket, 0)

    @staticmethod
    def validate(payload, field, unique_key):
        body = payload['body']
        if field == '__object__':
            if not isinstance(body, dict):
                raise ValueError('Expected object')
            return
        rows = body[field] if field else body
        if not isinstance(rows, list):
            raise ValueError('Expected list')
        for row in rows:
            if not isinstance(row, dict) or row.get(unique_key) is None:
                raise ValueError('Missing record ID')
        if field:
            if not isinstance(body.get('total_count'), int) or body['total_count'] < 0:
                raise ValueError('Missing/invalid endpoint total')
            if field == 'items' and not isinstance(body.get('incomplete_results'), bool):
                raise ValueError('Missing search completeness flag')
        if not isinstance(payload.get('fetched_at'), str):
            raise ValueError('Missing retrieval timestamp')
        nxt = payload.get('next')
        if nxt is not None and not isinstance(nxt, str):
            raise ValueError('Invalid next link')

    def page(self, url, field=None, unique_key='id', fresh=False):
        parsed = urlsplit(url)
        if parsed.scheme != 'https' or parsed.netloc != 'api.github.com' or parsed.username:
            raise FatalAPI('Refusing a pagination URL outside https://api.github.com')
        row = self.store.db.execute('SELECT payload,checksum,session FROM pages WHERE url=?',
                                    (url,)).fetchone()
        if row and (not fresh or row[2] == self.session_id):
            try:
                if digest(row[0]) != row[1]:
                    raise ValueError('Checksum mismatch')
                result = json.loads(row[0])
                self.validate(result, field, unique_key)
                self.used_pages[url] = result['fetched_at']
                return result
            except (ValueError, KeyError, TypeError):
                logging.warning('Invalid cached page; refetching %s', url)
        bucket = 'search' if parsed.path.startswith('/search/') else 'core'
        for attempt in range(self.retries + 1):
            for wait_bucket in (bucket, 'secondary'):
                remaining = self.store.get('wait:' + wait_bucket, 0) - time.time()
                if remaining > 0:
                    self.wait(remaining, 'Respecting saved API cooldown', wait_bucket)
            self.store.set('checkpoint', {'url': url, 'attempt': attempt + 1, 'time': now()})
            reason, pause = None, 0
            try:
                time.sleep(self.delay)
                response = self.http.get(url, timeout=(15, 90), allow_redirects=False)
                with response:
                    headers = {k.lower(): v for k, v in response.headers.items()}
                    status = response.status_code
                    if headers.get('x-ratelimit-remaining') == '0':
                        self.store.set('wait:' + bucket,
                                       float(headers.get('x-ratelimit-reset', time.time()+60)) + 2)
                    if status == 200:
                        result = {'body': response.json(),
                                  'next': response.links.get('next', {}).get('url'),
                                  'fetched_at': now(), 'query_url': url,
                                  'headers': {k: v for k, v in headers.items() if
                                              k.startswith('x-ratelimit-') or k in ('etag', 'link', 'date')}}
                        self.validate(result, field, unique_key)
                        encoded = dump(result)
                        # Cache and checkpoint commit together: crash cannot publish half a page.
                        with self.store.db:
                            self.store.db.execute('INSERT OR REPLACE INTO pages VALUES (?,?,?,?,?)',
                                                 (url, encoded, digest(encoded), result['fetched_at'], self.session_id))
                            self.store.db.execute('INSERT OR REPLACE INTO meta VALUES (?,?)',
                                                 ('checkpoint', dump({'url': url, 'next': result['next'],
                                                                       'saved_at': now()})))
                        self.used_pages[url] = result['fetched_at']
                        return result
                    try:
                        message = self.safe(response.json().get('message', ''))
                    except (ValueError, AttributeError):
                        message = 'non-JSON API error'
                    rate_limited = status == 429 or (status == 403 and (
                        headers.get('x-ratelimit-remaining') == '0' or 'retry-after' in headers
                        or 'rate limit' in message.lower() or 'abuse' in message.lower()))
                    if rate_limited:
                        pause = max(60 * 2 ** min(attempt, 5),
                                    self.store.get('wait:' + bucket, 0) - time.time())
                        if headers.get('retry-after'):
                            try:
                                retry_after = float(headers['retry-after'])
                            except ValueError:
                                retry_after = parsedate_to_datetime(headers['retry-after']).timestamp() - time.time()
                            pause = max(pause, retry_after)
                        reason = f'HTTP {status} rate limit: {message}'
                        # Persist even if retry budget is exhausted.
                        self.store.set('wait:secondary', time.time() + pause + 2)
                    elif status in (500, 502, 503, 504, 408):
                        reason = f'temporary HTTP {status}'
                        if headers.get('retry-after'):
                            try:
                                pause = max(0, float(headers['retry-after']))
                            except ValueError:
                                pause = max(0, parsedate_to_datetime(headers['retry-after']).timestamp() - time.time())
                    else:
                        hint = {401: 'invalid/expired token', 403: 'permission, SSO, or access denied',
                                404: 'missing resource or inaccessible with this token',
                                422: 'invalid query/validation failure (not retried)',
                                301: 'repository moved; use its canonical owner/name',
                                302: 'unexpected redirect'}.get(status, 'permanent API error')
                        error = f'HTTP {status}: {hint}; {message}'
                        if status in (401, 403):
                            raise FatalAPI(error)
                        raise CollectionError(error)
            except requests.exceptions.SSLError as exc:
                raise FatalAPI('TLS certificate/connection error; check certificates and network') from exc
            except (requests.exceptions.RequestException, ValueError, KeyError, TypeError) as exc:
                # Do not log request exception strings: they may contain credentials.
                reason = f'transport/JSON validation failure ({type(exc).__name__})'
            if attempt >= self.retries:
                raise CollectionError(f'Retry budget exhausted: {reason}; {url}')
            pause = max(pause, min(120, 2 ** (attempt + 1))) + random.uniform(0.2, 2.0)
            self.wait(pause, f'{reason}; retry {attempt + 1}/{self.retries}',
                      'secondary' if 'rate limit' in reason else bucket)
        raise AssertionError('unreachable')

    def paginate(self, path, params, label, field=None, unique_key='id', cap=None, fresh=False):
        url = API + path + '?' + urlencode(sorted({**params, 'per_page': 100}.items()))
        seen_urls, seen_pages, rows, total = set(), set(), {}, None
        page_no = 0
        while url:
            if url in seen_urls:
                raise CollectionError('Repeated pagination URL: ' + url)
            seen_urls.add(url)
            data = self.page(url, field, unique_key, fresh)
            page_no += 1
            body = data['body']
            batch = body[field] if field else body
            if field:
                expected = body['total_count']
                if cap and (expected >= cap or body.get('incomplete_results', False)):
                    raise SplitNeeded(f'total={expected}; incomplete={body.get("incomplete_results", False)}')
                if total is not None and expected != total:
                    raise SplitNeeded('Endpoint total changed during pagination')
                total = expected
            signature = digest(dump(sorted(str(item[unique_key]) for item in batch)))
            if batch and signature in seen_pages:
                raise CollectionError('Repeated page contents detected')
            seen_pages.add(signature)
            for item in batch:
                key = str(item[unique_key])
                if key in rows:
                    logging.warning('%s duplicate ID %s; deduplicated', label, key)
                rows[key] = {**item, '_retrieved_at': data['fetched_at']}
            logging.info('%s | page %d | %d records this page | %d unique downloaded',
                         label, page_no, len(batch), len(rows))
            url = data['next']
            if url and not batch:
                raise CollectionError('Empty page with a next link')
        if total is not None and len(rows) != total:
            raise SplitNeeded(f'Count mismatch: {len(rows)} unique vs endpoint total {total}')
        return list(rows.values())


def actor(user, overrides):
    user = user or {}
    uid, login = user.get('id'), user.get('login', '')
    override = overrides.get(str(uid), overrides.get(login.lower()))
    if override:
        label, reason = override, 'manual_override'
    elif user.get('type') == 'Bot':
        label, reason = 'bot', 'api_type_Bot'
    elif login.lower().endswith('[bot]'):
        label, reason = 'bot', 'login_suffix_[bot]'
    elif uid is None or login in ('ghost', 'mannequin') or user.get('type') == 'Mannequin':
        label, reason = 'unknown', 'missing_or_placeholder_identity'
    else:
        label, reason = 'other_user', 'not_identified_as_bot'
    return {'account_id': uid if uid is not None else '', 'login': login,
            'account_label': label, 'label_reason': reason}


def period_start(value, grain):
    day = value.replace(hour=0, minute=0, second=0, microsecond=0)
    return day - timedelta(days=day.weekday()) if grain == 'week' else day.replace(day=1)


def period_next(value, grain):
    if grain == 'week':
        return value + timedelta(days=7)
    return (value.replace(day=28) + timedelta(days=4)).replace(day=1)


def bins(start, end):
    for grain in ('week', 'month'):
        point = period_start(start, grain)
        while point < end:
            nxt = period_next(point, grain)
            yield {'period_type': grain, 'period_start': iso(point),
                   'observed_start': iso(max(point, start)), 'observed_end': iso(min(nxt, end)),
                   'partial_period': point < start or nxt > end}
            point = nxt


def csv_write(path, rows, fields):
    with open(path, 'w', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)
        stream.flush()
        os.fsync(stream.fileno())


class Collector:
    def __init__(self, args, client, store, scope):
        self.args, self.client, self.store, self.scope = args, client, store, scope
        self.start, self.end = dt(args.start), dt(args.end)
        self.gaps = []
        self.completed = []
        self.base = '/repos/' + args.repo
        self.old_failed = store.get('failed_intervals', [])

    def fresh(self, kind, a, b):
        if self.args.refresh_all:
            return True
        if self.args.refresh_start:
            if kind == 'comments' or (a < dt(self.args.refresh_end) and b > dt(self.args.refresh_start)):
                return True
        return self.args.retry_failed and any(
            x['kind'] == kind and a < dt(x['end']) and b > dt(x['start']) for x in self.old_failed)

    def collect(self, kind, a, b, depth=0):
        label = f'{kind} [{iso(a)}, {iso(b)})'
        logging.info('START %s', label)
        upper = iso(b - timedelta(seconds=1))
        fresh = self.fresh(kind, a, b)
        try:
            if kind == 'commit':
                rows = self.client.paginate(self.base + '/commits',
                    {'sha': self.scope['commit_head_sha'], 'since': iso(a-timedelta(seconds=1)),
                     'until': iso(b)}, label, unique_key='sha', fresh=fresh)
                rows = [r for r in rows if a <= dt(r['commit']['committer']['date']) < b]
            elif kind in ('issue_opened', 'pr_opened'):
                typ = 'issue' if kind == 'issue_opened' else 'pr'
                rows = self.client.paginate('/search/issues',
                    {'q': f'repo:{self.args.repo} is:{typ} created:{iso(a)}..{upper}',
                     'sort': 'created', 'order': 'asc'}, label, field='items', cap=1000, fresh=fresh)
                if any(not a <= dt(r['created_at']) < b for r in rows):
                    raise CollectionError('Search returned records outside requested interval')
            elif kind.startswith('workflow:'):
                event = kind.split(':')[1]
                rows = self.client.paginate(self.base + '/actions/runs',
                    {'event': event, 'created': f'{iso(a)}..{upper}'}, label,
                    field='workflow_runs', cap=1000, fresh=fresh)
                if any(not a <= dt(r['created_at']) < b or r['event'] != event for r in rows):
                    raise CollectionError('Workflow response does not match interval/event')
            else:
                # since filters UPDATED time, so use start-1 sec, then filter CREATED locally.
                # Fetch all pages, including post-cutoff comments, to avoid unsafe early stopping.
                rows = self.client.paginate(self.base + '/issues/comments',
                    {'since': iso(self.start-timedelta(seconds=1)), 'sort': 'created', 'direction': 'asc'},
                    label, fresh=fresh)
                rows = [r for r in rows if self.start <= dt(r['created_at']) < self.end]
            self.completed.append({'kind': kind, 'start': iso(a), 'end': iso(b), 'count': len(rows)})
            self.store.audit(kind, a, b, 'complete', len(rows))
            logging.info('COMPLETE %s | %d unique records', label, len(rows))
            return rows
        except SplitNeeded as exc:
            seconds = int((b-a).total_seconds())
            if seconds > 1:
                mid = a + timedelta(seconds=seconds//2)
                logging.info('SPLIT %s | %s', label, exc)
                return self.collect(kind, a, mid, depth+1) + self.collect(kind, mid, b, depth+1)
            return self.fail(kind, a, b, f'Unsplittable one-second interval: {exc}')
        except FatalAPI:
            raise
        except (CollectionError, KeyError, TypeError, ValueError) as exc:
            return self.fail(kind, a, b, self.client.safe(exc))

    def fail(self, kind, a, b, reason):
        gap = {'kind': kind, 'start': iso(a), 'end': iso(b), 'reason': reason}
        self.gaps.append(gap)
        self.store.set('failed_intervals', self.gaps + self.old_failed)
        self.store.audit(kind, a, b, 'failed', reason)
        logging.error('GAP %s [%s,%s): %s', kind, iso(a), iso(b), reason)
        return []

    def run(self):
        results = {}
        for kind in (*KINDS, 'workflow:push', 'workflow:pull_request', 'comments'):
            unique = {}
            a = self.start
            while a < self.end:
                b = self.end if kind == 'comments' else min(a+timedelta(days=7), self.end)
                for row in self.collect(kind, a, b):
                    unique[str(row['sha'] if kind == 'commit' else row['id'])] = row
                a = b
            results[kind] = list(unique.values())
        self.store.set('failed_intervals', self.gaps)
        return results


def export(args, collector, data, overrides):
    root = Path(args.out) / 'exports'
    root.mkdir(exist_ok=True)
    temp = Path(tempfile.mkdtemp(prefix='.building-', dir=root))
    stamp = datetime.now(UTC).strftime('%Y%m%dT%H%M%S') + '-' + str(time.time_ns())[-8:]
    start, end = collector.start, collector.end
    account_fields = ['account_id', 'login', 'account_label', 'label_reason']
    period_fields = ['period_type', 'period_start', 'observed_start', 'observed_end', 'partial_period']
    periods = list(bins(start, end))
    # Per-metric completeness: an incomplete observation is not a reliable zero.
    contribution_complete = not any(g['kind'] in KINDS for g in collector.gaps)
    response_complete = not any(g['kind'] in ('issue_opened', 'comments') for g in collector.gaps)
    actions_complete = not any(g['kind'].startswith('workflow:') for g in collector.gaps)
    activities = []
    for kind in KINDS:
        for r in data[kind]:
            is_commit = kind == 'commit'
            activities.append({'activity_type': kind, 'activity_id': r['sha'] if is_commit else r['id'],
                'created_at': r['commit']['committer']['date'] if is_commit else r['created_at'],
                **actor(r.get('author') if is_commit else r.get('user'), overrides),
                'url': r['html_url'], 'retrieved_at': r['_retrieved_at']})
    activities.sort(key=lambda r: (r['created_at'], r['activity_type'], str(r['activity_id'])))
    csv_write(temp/'activities.csv', activities,
              ['activity_type','activity_id','created_at', *account_fields,'url','retrieved_at'])
    contributors = {}
    per_account = defaultdict(Counter)
    totals = Counter()
    unique_accounts = defaultdict(set)
    account_period_totals = defaultdict(Counter)
    for r in activities:
        uid = r['account_id']
        valid = uid != '' and r['account_label'] != 'unknown'
        if valid:
            account = contributors.setdefault(uid, {**{k: r[k] for k in account_fields},
                **{k: 0 for k in KINDS}, 'total_contributions': 0,
                'first_activity': r['created_at'], 'last_activity': r['created_at']})
            account[r['activity_type']] += 1
            account['total_contributions'] += 1
            account['last_activity'] = r['created_at']
        for grain in ('week', 'month'):
            period = iso(period_start(dt(r['created_at']), grain))
            key = (grain, period, r['account_label'])
            totals[(*key, r['activity_type'])] += 1
            if valid:
                unique_accounts[key].add(uid)
                account_period_totals[key][uid] += 1
                per_account[(grain, period, uid)][r['activity_type']] += 1
    contributor_rows = sorted(contributors.values(), key=lambda r: (-r['total_contributions'], str(r['account_id'])))
    for r in contributor_rows:
        r['data_complete'] = contribution_complete
    fields = [*account_fields, *KINDS,'total_contributions','first_activity','last_activity','data_complete']
    csv_write(temp/'contributors_all.csv', contributor_rows, fields)
    csv_write(temp/'contributors_more_than_one.csv',
              [r for r in contributor_rows if r['total_contributions'] > 1], fields)
    repo_rows, person_rows = [], []
    for p in periods:
        for label in LABELS:
            key = (p['period_type'], p['period_start'], label)
            repo_rows.append({**p, 'account_label': label,
                **{k: totals[(*key, k)] for k in KINDS},
                'total_contributions': sum(totals[(*key, k)] for k in KINDS),
                'unique_identified_accounts': len(unique_accounts[key]),
                'accounts_more_than_one_in_period': sum(v > 1 for v in account_period_totals[key].values()),
                'data_complete': contribution_complete})
        # Zero-filled for all known contributors, including inactive periods.
        for uid, account in contributors.items():
            counts = per_account[(p['period_type'], p['period_start'], uid)]
            person_rows.append({**p, **{k: account[k] for k in account_fields},
                **{k: counts[k] for k in KINDS}, 'total_contributions': sum(counts.values()),
                'more_than_one_in_period': sum(counts.values()) > 1,
                'more_than_one_full_window': account['total_contributions'] > 1,
                'data_complete': contribution_complete})
    csv_write(temp/'activity_period_counts.csv', repo_rows,
              [*period_fields,'account_label',*KINDS,'total_contributions',
               'unique_identified_accounts','accounts_more_than_one_in_period','data_complete'])
    csv_write(temp/'contributor_period_counts.csv', person_rows,
              [*period_fields,*account_fields,*KINDS,'total_contributions',
               'more_than_one_in_period','more_than_one_full_window','data_complete'])
    issues = {int(r['number']): r for r in data['issue_opened']}
    replies = defaultdict(list)
    for c in data['comments']:
        number = int(c['issue_url'].rstrip('/').split('/')[-1])
        if number in issues:
            replies[number].append(c)
    response_rows = []
    grouped_responses = defaultdict(list)
    for number, issue in issues.items():
        opener = actor(issue.get('user'), overrides)
        identifiable = opener['account_id'] != '' and opener['account_label'] != 'unknown'
        first = {}
        if identifiable:
            for c in sorted(replies[number], key=lambda r: (r['created_at'], r['id'])):
                responder = actor(c.get('user'), overrides)
                if responder['account_id'] == opener['account_id']:
                    continue
                if dt(c['created_at']) < dt(issue['created_at']):
                    continue
                # Missing identity is kept explicitly unknown, not called a human reply.
                first.setdefault(responder['account_label'], (c, responder))
                first.setdefault('any', (c, responder))
        for label in (*LABELS, 'any'):
            selected = first.get(label)
            c, responder = selected if selected else ({}, {})
            delay = (dt(c['created_at']) - dt(issue['created_at'])).total_seconds()/3600 if c else ''
            status = ('identity_unresolved' if not identifiable else
                      'observed' if c else 'unresolved_collection_gap' if not response_complete else 'censored')
            row = {'issue_id': issue['id'], 'issue_number': number, 'opened_at': issue['created_at'],
                'opener_id': opener['account_id'], 'opener_label': opener['account_label'],
                'response_class': label, 'response_status': status,
                'comment_id': c.get('id',''), 'responded_at': c.get('created_at',''),
                'responder_id': responder.get('account_id',''), 'responder_login': responder.get('login',''),
                'responder_label': responder.get('account_label',''),
                'response_hours': delay, 'follow_up_hours': (end-dt(issue['created_at'])).total_seconds()/3600,
                'data_complete': response_complete, 'issue_url': issue['html_url']}
            response_rows.append(row)
            for grain in ('week', 'month'):
                grouped_responses[(grain, iso(period_start(dt(issue['created_at']), grain)), label)].append(row)
    response_fields = ['issue_id','issue_number','opened_at','opener_id','opener_label','response_class',
        'response_status','comment_id','responded_at','responder_id','responder_login','responder_label',
        'response_hours','follow_up_hours','data_complete','issue_url']
    csv_write(temp/'issue_responses.csv', response_rows, response_fields)
    summary = []
    for p in periods:
        for label in (*LABELS, 'any'):
            rs = grouped_responses[(p['period_type'], p['period_start'], label)]
            hours = [r['response_hours'] for r in rs if r['response_status'] == 'observed']
            summary.append({**p, 'response_class': label, 'issues_opened': len(rs),
                'observed_responses': len(hours),
                'censored_no_response': sum(r['response_status']=='censored' for r in rs),
                'identity_unresolved': sum(r['response_status']=='identity_unresolved' for r in rs),
                'collection_unresolved': sum(r['response_status']=='unresolved_collection_gap' for r in rs),
                'mean_response_hours': statistics.mean(hours) if hours else '',
                'median_response_hours': statistics.median(hours) if hours else '',
                'data_complete': response_complete})
    csv_write(temp/'response_period_summary.csv', summary,
              [*period_fields,'response_class','issues_opened','observed_responses','censored_no_response',
               'identity_unresolved','collection_unresolved','mean_response_hours','median_response_hours','data_complete'])
    workflow_rows, workflow_counts = [], Counter()
    statuses, conclusions = set(STATUSES), set(CONCLUSIONS)
    for event in ('push','pull_request'):
        for r in data['workflow:'+event]:
            status, conclusion = r.get('status') or 'unknown', r.get('conclusion') or 'none'
            statuses.add(status)
            conclusions.add(conclusion)
            workflow_rows.append({'run_id': r['id'], 'event': event,
                'event_action': 'activity_action_unknown' if event=='pull_request' else 'not_applicable',
                'created_at': r['created_at'], 'updated_at': r.get('updated_at',''),
                'status': status, 'conclusion': conclusion, 'run_attempt': r.get('run_attempt',1),
                'workflow_id': r.get('workflow_id',''), 'workflow_name': r.get('name',''),
                'head_sha': r.get('head_sha',''),
                'pull_request_numbers': ';'.join(str(pr['number']) for pr in r.get('pull_requests',[])),
                **actor(r.get('actor'), overrides), 'retrieved_at': r['_retrieved_at'], 'url': r['html_url']})
            for grain in ('week','month'):
                period = iso(period_start(dt(r['created_at']),grain))
                workflow_counts[(grain,period,event,'status',status)] += 1
                workflow_counts[(grain,period,event,'conclusion',conclusion)] += 1
    csv_write(temp/'workflow_runs.csv', workflow_rows,
              ['run_id','event','event_action','created_at','updated_at','status','conclusion','run_attempt',
               'workflow_id','workflow_name','head_sha','pull_request_numbers',*account_fields,'retrieved_at','url'])
    wf_summary = []
    for p in periods:
        for event in ('push','pull_request'):
            for dimension, values in (('status',statuses),('conclusion',conclusions)):
                for value in sorted(values):
                    wf_summary.append({**p,'event':event,'dimension':dimension,'value':value,
                        'count':workflow_counts[(p['period_type'],p['period_start'],event,dimension,value)],
                        'data_complete':actions_complete,
                        'event_action':'activity_action_unknown' if event=='pull_request' else 'not_applicable'})
    csv_write(temp/'workflow_period_counts.csv', wf_summary,
              [*period_fields,'event','event_action','dimension','value','count','data_complete'])
    timestamps = sorted(collector.client.used_pages.values())
    manifest = {'scope':collector.scope,'exported_at':now(),'api_version':VERSION,
        'collection_status':'incomplete' if collector.gaps else 'complete_for_api_visible_scope',
        'historical_archive_completeness':'not_verifiable',
        'pull_request_opened_only_available':False,
        'page_retrieval_earliest':timestamps[0] if timestamps else None,
        'page_retrieval_latest':timestamps[-1] if timestamps else None,
        'mixed_cached_snapshots':len(set(timestamps))>1,
        'gaps':collector.gaps,'completed_intervals':collector.completed,
        'counts':{k:len(v) for k,v in data.items()},
        'unattributed_contributions':sum(r['account_label']=='unknown' for r in activities),
        'bot_overrides':overrides,
        'definitions':{'contributions':list(KINDS),'threshold':'total_contributions > 1',
            'response':'first non-author comment per responder class before end; cohort by issue opening date',
            'week':'Monday 00:00 UTC; partial first/last bins',
            'month':'calendar month UTC; partial first/last bins',
            'workflows':'one latest representation per run ID; current state at page retrieval, not at cutoff',
            'other_user':'not identified as bot; not proof of human identity'},
        'limitations':['No pull_request action=opened field in workflow-runs REST response',
            'No reconstruction of deleted or inaccessible events',
            'No authoritative total for commit/comment list endpoints',
            'Search indexing and concurrent changes can affect results',
            'Unlinked/placeholder identities excluded from account contributor tables',
            'Response times are censored at end; observed-only means can bias downward',
            'Any gap makes associated metric data_complete false; zero is not reliable then'],
        'query_metadata':'Exact URLs, parameters, timestamps and rate-limit headers are in cache.sqlite3 pages',
        'reproduce_command':'Use same arguments and cache; --refresh-all fetches newer mutable states'}
    atomic_json(temp/'manifest.json', manifest)
    final = root/stamp
    os.replace(temp,final)
    atomic_json(Path(args.out)/'latest.json', {'export_directory':str(final.resolve()),
                'status':manifest['collection_status'],'updated_at':now()},backup=True)
    return final


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--repo', default='openai/codex')
    parser.add_argument('--start',default='2025-10-22T00:00:00Z')
    parser.add_argument('--end',default='2026-10-21T00:00:00Z')
    parser.add_argument('--out',default='codex_activity')
    parser.add_argument('--branch',help='Override default branch (HEAD SHA is pinned on first run)')
    parser.add_argument('--refresh-all',action='store_true')
    parser.add_argument('--refresh-start')
    parser.add_argument('--refresh-end')
    parser.add_argument('--retry-failed',action='store_true')
    parser.add_argument('--bot-overrides',type=Path,help='JSON object: account ID or lowercase login -> bot/other_user/unknown')
    parser.add_argument('--max-retries',type=int,default=8)
    parser.add_argument('--request-delay',type=float,default=0.25)
    args = parser.parse_args(argv)
    try:
        start,end=dt(args.start),dt(args.end)
        if start>=end:
            raise ValueError('start must precede end')
        if bool(args.refresh_start)!=bool(args.refresh_end):
            raise ValueError('Provide both --refresh-start and --refresh-end')
        if args.refresh_start and not start<=dt(args.refresh_start)<dt(args.refresh_end)<=end:
            raise ValueError('Refresh interval must be inside observation window')
        if args.max_retries<0 or args.request_delay<0:
            raise ValueError('Retries/delay cannot be negative')
        parts=args.repo.split('/')
        if len(parts)!=2 or any(not p or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-' for c in p) for p in parts):
            raise ValueError('repo must be owner/name')
        overrides=json.loads(args.bot_overrides.read_text()) if args.bot_overrides else {}
        if not isinstance(overrides,dict) or any(v not in LABELS for v in overrides.values()):
            raise ValueError('Invalid bot overrides')
        overrides={str(k).lower():v for k,v in overrides.items()}
    except (ValueError,OSError) as exc:
        parser.error(str(exc))
    args.start,args.end=iso(start),iso(end)
    root=Path(args.out)
    root.mkdir(parents=True,exist_ok=True)
    # OS lock releases automatically after a crash; no stale lockfile removal needed.
    lock=open(root/'collector.lock','a+')
    try:
        if os.name=='nt':
            import msvcrt
            lock.seek(0)
            lock.write('0')
            lock.flush()
            lock.seek(0)
            msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1)
        else:
            import fcntl
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except OSError:
        print('Another collector is using this output directory.',file=sys.stderr)
        lock.close()
        return 2
    logging.basicConfig(level=logging.INFO,format='%(asctime)s UTC %(levelname)s %(message)s',
                        handlers=[logging.StreamHandler(),logging.FileHandler(root/'progress.log',encoding='utf-8')],force=True)
    logging.Formatter.converter=time.gmtime
    store=Store(root/'cache.sqlite3')
    try:
        requested={'repo':args.repo,'start':args.start,'end':args.end,'requested_branch':args.branch,
                   'schema_version':1}
        scope=store.get('scope')
        if scope and any(scope.get(k)!=v for k,v in requested.items()):
            raise CollectionError('Output directory has a different scope. Use a new --out directory.')
        token=os.environ.get()
        if not token:
            if not sys.stdin.isatty():
                raise CollectionError('Set GITHUB_TOKEN or GH_TOKEN; no interactive terminal available')
            token=getpass.getpass('GitHub token (hidden): ').strip()
        if not token:
            raise CollectionError('A GitHub token is required for this large collection')
        client=Client(store,token,args.max_retries,args.request_delay)
        if not scope:
            repo=client.page(API+'/repos/'+args.repo,field='__object__')['body']
            branch=args.branch or repo['default_branch']
            head=client.page(API+'/repos/'+args.repo+'/commits/'+quote(branch,safe=''),field='__object__')['body']['sha']
            scope={**requested,'resolved_branch':branch,'commit_head_sha':head,'initialized_at':now()}
            store.set('scope',scope)
        logging.info('Scope %s [%s,%s); branch %s pinned at %s',args.repo,args.start,args.end,
                     scope['resolved_branch'],scope['commit_head_sha'])
        collector=Collector(args,client,store,scope)
        data=collector.run()
        final=export(args,collector,data,overrides)
        logging.info('%s: %s', 'INCOMPLETE (see manifest gaps)' if collector.gaps else
                     'COMPLETE for API-visible scope; PR opened-only unavailable', final)
        return 2 if collector.gaps else 0
    except KeyboardInterrupt:
        logging.warning('Interrupted; validated pages remain saved. Rerun the same command to resume.')
        return 130
    except (CollectionError,OSError,sqlite3.Error,KeyError) as exc:
        # All request-derived error messages have already been sanitized.
        logging.error('STOPPED: %s. Cached progress preserved; no successful export claimed.',exc)
        return 2
    finally:
        store.db.close()
        lock.close()


if __name__=='__main__':
    sys.exit(main())
