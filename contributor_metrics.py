#!/usr/bin/env python3
"""Contributor activity metrics: commits, issues opened, pull requests opened.
Python 3.9+, standard library only. No plotting or automatic classification.

RUN (until is exclusive; all dates UTC):
  python3 contributor_metrics.py --since 2025-10-22 --until 2026-10-22
RECOVERY of missing recent issue/PR data (reuses existing commits):
  python3 contributor_metrics.py --since 2025-10-22 --until 2026-10-21 --out contributor_results --recover-openings-since 2026-07-01
The recovery request uses the API updated-since filter and newest-first creation
order. It may also return older items updated recently. Merge by issue ID prevents
counting overlaps twice. Opening timestamps remain created_at. All CSV metrics
are rebuilt, with previous outputs backed up. Recovery pages are resumable and
supplemental data are retained on later runs without the flag. A missing next
link means traversal ended, not independent proof of dataset completeness.

Use GITHUB_TOKEN or GH_TOKEN (legacy token also supported). Never paste tokens
into this file. Use --out contributor_results to reuse the original commit cache.
Do not run two collectors against the same output directory simultaneously.

OUTPUTS:
  contributors.csv: one row per identity; combined metrics plus per-type metrics
    prefixed commit_, issue_opened_, pr_opened_. Includes dormant identities with
    historical activity but zero activity in the selected window.
  weekly.csv, monthly.csv: one row per identity per calendar period, including
    zero-activity periods. Counts and within-period gaps are combined and per-type.
    Streamed to disk to limit memory use. Weeks start Monday; months on day 1.
  events.csv: one row per eligible historical event, with activity_type, timestamp,
    contributor_id, event_id, URL and in_observation_window flag.
  commits.csv: same event schema restricted to commits (changed from old schema).
  methodology.json: settings, snapshot, definitions and collection limitations.
  cache/: resumable atomic page files. Existing page_*.json commits are reused.
    Issue/PR v3 caches store GitHub next links (including opaque cursor parameters).
    Old v2 issue/PR caches lack response links and must be re-fetched once; they
    are retained untouched. The 1,000-item numeric-page failure is avoided by
    following response Link headers instead of constructing page=N requests.

METRICS (all times measured in days):
  count_window / count_historical: number of events in [since, until) / before until.
  first_activity / latest_activity: earliest/latest eligible historical event.
  tenure_days / recency_days: until minus first/latest historical activity.
  mean_gap_days_window / historical: mean consecutive gap = (last-first)/(n-1).
    Blank for fewer than two events. Within-period gaps exclude cross-boundary gaps.
  active_weeks / months: periods with >=1 event inside the observation window.
  active_week/month_fraction: active periods / all calendar periods in window.
    Includes zero periods and periods before someone's first observed activity.
  mean_events_per_week/month: window count / number of calendar periods observed.
  events_per_30_days_since_entry: window count / days from max(since, first activity)
    to until * 30. Helps compare newcomers with established contributors; a short
    exposure can inflate this rate. exposure_days_since_entry reports the denominator.
  Counts of each type and per-type recency/tenure prevent mixed totals hiding roles.

SCOPE:
  No sampling: fetch all available history before the end date, then filter locally.
  Commits: reachable from a frozen default-branch tip (or --ref); includes merge
  commits unless --exclude-merges. Attribution is to author, timestamp defaults
  to git committer date (--date-field author is available). Neither date is a
  verified push/merge time. Historical branch membership is NOT reconstructed.
  Issues + PRs: GET /repos/{owner}/{repo}/issues, state=all, sort=created, direction=asc.
  GitHub includes PRs here: pull_request field => pr_opened; otherwise issue_opened.
  Use created_at, NOT updated_at or closed_at. Includes closed issues, draft,
  closed/unmerged and merged PR openings. Each opening counts once. PRs are not
  additionally counted as issues; PR opening and its eventual commits are separate
  activity events, not independent units of work. Reopenings are not counted.
  New collection fixes the cutoff to collection start; old commit caches keep their
  original cutoff. Cached issue pages cover that cutoff, allowing earlier end dates.
  Ascending creation order reduces pagination shifts from newly created items;
  deleted/transferred/inaccessible items and concurrent changes can still affect
  coverage. REST issue lists are not immutable historical snapshots.
  Group linked authors/openers by numeric GitHub account ID across all three types.
  Unlinked commits use hashed email (or SHA); unknown issue/PR authors get separate
  unresolved event identities. No inferred person merging or co-author attribution.
  Bots are flagged by API type Bot or [bot] login suffix; --exclude-bots filters
  these candidates only. Manually validate bots, aliases and shared accounts.
  Reviews/comments/discussions are excluded. First/last activity refer only to the
  three selected types and accessible history. Counts measure volume, not impact.
  Interpret 'dormant' within this scope, and validate 'key' status qualitatively.
  CSV text originates on GitHub: import it as data, not spreadsheet formulas.

Docs: https://docs.github.com/en/rest/issues/issues#list-repository-issues
      https://docs.github.com/en/rest/commits/commits#list-commits
"""
import argparse
import csv
import hashlib
from http.client import IncompleteRead, RemoteDisconnected
from itertools import chain
import shutil
import json
import os
from pathlib import Path
import re
import sys
import time
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode, urlsplit
from urllib.request import Request, urlopen

UTC = timezone.utc


def dt(value):
    result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    return result.replace(tzinfo=UTC) if result.tzinfo is None else result.astimezone(UTC)


def iso(value):
    return value.isoformat().replace('+00:00', 'Z')


def save_json(path, data):
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2), encoding='utf-8')
    temp.replace(path)


def api_path(url):
    """Accept only GitHub API links, keeping the authentication token on GitHub."""
    parts = urlsplit(url)
    if parts.scheme or parts.netloc:
        if parts.scheme != 'https' or parts.netloc != 'api.github.com':
            raise ValueError('Unexpected pagination URL origin; request stopped.')
    if not parts.path.startswith('/') or parts.path.startswith('//') or parts.fragment:
        raise ValueError('Invalid API pagination path.')
    return parts.path + ('?' + parts.query if parts.query else '')


def next_link(header):
    for segment in header.split(','):
        match = re.search(r'<([^>]+)>\s*;\s*rel="([^"]+)"', segment)
        if match and 'next' in match.group(2).split():
            return api_path(match.group(1))
    return None


def api(path, with_next=False):
    path = api_path(path)
    headers = {'Accept': 'application/vnd.github+json', 'User-Agent': 'contributor-metrics',
               'X-GitHub-Api-Version': '2022-11-28'}
    token = os.environ.get()
    if token:
        headers['Authorization'] = 'Bearer ' + token
    for attempt in range(9):
        delay = min(60, 2 ** attempt)
        try:
            with urlopen(Request('https://api.github.com' + path, headers=headers), timeout=60) as response:
                data = json.load(response)
                if with_next:
                    return data, next_link(response.headers.get('Link', ''))
                return data
        except HTTPError as exc:
            message = exc.read().decode('utf-8', errors='replace')
            limited = exc.code == 429 or (exc.code == 403 and (
                exc.headers.get('X-RateLimit-Remaining') == '0' or
                'rate limit' in message.lower() or 'secondary rate' in message.lower()))
            if not limited and exc.code not in (500, 502, 503, 504):
                raise RuntimeError(f'GitHub HTTP {exc.code}: {message[:500]}') from None
            if limited:
                delay = max(60, delay)
                if exc.headers.get('Retry-After', '').isdigit():
                    delay = max(delay, int(exc.headers['Retry-After']))
                if exc.headers.get('X-RateLimit-Remaining') == '0':
                    delay = max(delay, float(exc.headers.get('X-RateLimit-Reset', time.time())) - time.time() + 2)
        except (URLError, TimeoutError, ConnectionError, IncompleteRead, RemoteDisconnected):
            pass
        if attempt == 8:
            raise RuntimeError('Retries exhausted. Rerun the same command to resume cached pages.')
        print(f'Temporary API/network limit; retrying in {delay:.0f}s.', flush=True)
        # Small sleeps make Ctrl+C responsive even during a long rate-limit wait.
        deadline = time.monotonic() + delay
        while time.monotonic() < deadline:
            time.sleep(min(5, max(0, deadline - time.monotonic())))


def collect(args, cache):
    state_path = cache / 'snapshot.json'
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state['repo'] != args.repo or state['requested_ref'] != args.ref:
            raise ValueError('Cached repo/ref differs; choose a new --out directory.')
    else:
        repo = '/repos/' + args.repo
        ref = args.ref or api(repo)['default_branch']
        tip = api(repo + '/commits/' + quote(ref, safe=''))['sha']
        state = {'repo': args.repo, 'requested_ref': args.ref, 'resolved_ref': ref,
                 'snapshot_sha': tip, 'collection_started_at': iso(datetime.now(UTC))}
        save_json(state_path, state)
    commits = {}
    page = 1
    while True:
        target = cache / f'page_{page:06}.json'
        if target.exists():
            batch = json.loads(target.read_text())
        else:
            params = urlencode({'sha': state['snapshot_sha'], 'per_page': 100, 'page': page})
            batch = api('/repos/' + args.repo + '/commits?' + params)
            if not isinstance(batch, list):
                raise RuntimeError('Unexpected commits response; no metrics written.')
            save_json(target, batch)
        for commit in batch:
            commits[commit['sha']] = commit
        print(f'Page {page}: {len(commits)} unique commits cached', flush=True)
        if len(batch) < 100:
            break
        page += 1
    return state, list(commits.values())


TYPES = ('commit', 'issue_opened', 'pr_opened')


def collect_openings(args, cache, cutoff, updated_since=None):
    """Follow GitHub's opaque next links, not numeric page parameters."""
    result = {}
    query = {'state': 'all', 'sort': 'created',
             'direction': 'desc' if updated_since else 'asc', 'per_page': 100}
    if updated_since:
        query['since'] = iso(updated_since)
    params = urlencode(query)
    prefix = ('recovery_' + hashlib.sha256(params.encode()).hexdigest()[:16]
              if updated_since else 'openings_v3')
    request_path = '/repos/' + args.repo + '/issues?' + params
    page = 1
    visited = set()
    if not updated_since and not (cache / 'openings_v3_000001.json').exists() and any(cache.glob('openings_v2_*.json')):
        print('Upgrading issue/PR pagination: re-reading early pages to obtain cursor links. '
              'Commit cache is reused; old issue/PR files are retained.', flush=True)
    while request_path:
        if request_path in visited:
            raise RuntimeError('Repeated pagination link; stopped to avoid an infinite loop.')
        visited.add(request_path)
        path = cache / f'{prefix}_{page:06}.json'
        if path.exists():
            record = json.loads(path.read_text())
            if record.get('request_path') != request_path:
                raise ValueError('Issue/PR cursor cache does not match the next request; '
                                 'choose a new output directory.')
            batch, following = record['items'], record['next_path']
            source = 'cache'
        else:
            batch, following = api(request_path, with_next=True)
            if not isinstance(batch, list):
                raise RuntimeError('Unexpected issue/PR response; no metrics written.')
            # Save data AND next cursor atomically so interrupted runs can resume.
            save_json(path, {'request_path': request_path, 'items': batch,
                             'next_path': following})
            source = 'download'
        for item in batch:
            if dt(item['created_at']) < cutoff:
                result[item['id']] = item
        print(f'Issues/PRs batch {page} ({source}): {len(result)} openings before cutoff', flush=True)
        if not updated_since and any(dt(x['created_at']) >= cutoff for x in batch):
            break
        # A short batch is not a reliable termination signal; use the next link.
        request_path = api_path(following) if following else None
        page += 1
    return list(result.values())


def normalize(commits, openings, args, end):
    events = {}
    def add(user, stamp, kind, event_id, url, merge=False, email=''):
        if stamp >= end:
            return
        login = user.get('login', '')
        bot = user.get('type') == 'Bot' or login.lower().endswith('[bot]')
        if (args.exclude_bots and bot) or (args.exclude_merges and merge):
            return
        if user.get('id') is not None:
            identity, status = 'github:' + str(user['id']), 'linked_account'
        elif kind == 'commit' and email:
            identity = 'unlinked:' + hashlib.sha256(email.strip().lower().encode()).hexdigest()
            status = 'unlinked_email'
        else:
            identity, status = 'unresolved:' + event_id, 'unresolved_event'
        events[event_id] = {'contributor_id': identity, 'login': login,
            'identity_status': status, 'bot_candidate': bot, 'activity_type': kind,
            'event_id': event_id, 'timestamp': iso(stamp), 'url': url, 'is_merge': merge}
    for c in commits:
        author = c['commit']['author'] or {}
        add(c.get('author') or {}, dt(c['commit'][args.date_field]['date']),
            'commit', 'commit:' + c['sha'], c.get('html_url', ''),
            len(c.get('parents', [])) > 1, author.get('email') or '')
    for item in openings:
        kind = 'pr_opened' if 'pull_request' in item else 'issue_opened'
        add(item.get('user') or {}, dt(item['created_at']), kind,
            kind + ':' + str(item['id']), item.get('html_url', ''))
    return sorted(events.values(), key=lambda e: (dt(e['timestamp']), e['event_id']))


def gap(times):
    return round((times[-1] - times[0]).total_seconds() / 86400 / (len(times) - 1), 8) if len(times) >= 2 else ''


def period_start(t, kind):
    t = t.replace(hour=0, minute=0, second=0, microsecond=0)
    return t - timedelta(days=t.weekday()) if kind == 'week' else t.replace(day=1)


def next_period(t, kind):
    if kind == 'week':
        return t + timedelta(days=7)
    return t.replace(year=t.year + (t.month == 12), month=t.month % 12 + 1)


def periods(start, end, kind):
    result = []
    p = period_start(start, kind)
    while p < end:
        q = next_period(p, kind)
        result.append((p, max(start, p), min(end, q)))
        p = q
    return result


def metrics(times, start, end, buckets):
    window = [t for t in times if start <= t < end]
    exposure = (end - max(start, times[0])).total_seconds()/86400 if times else None
    row = {'count_historical': len(times), 'count_window': len(window),
           'first_activity': iso(times[0]) if times else '',
           'latest_activity': iso(times[-1]) if times else '',
           'tenure_days': (end-times[0]).total_seconds()/86400 if times else '',
           'recency_days': (end-times[-1]).total_seconds()/86400 if times else '',
           'mean_gap_days_historical': gap(times), 'mean_gap_days_window': gap(window),
           'exposure_days_since_entry': exposure if exposure is not None else '',
           'events_per_30_days_since_entry': len(window)/exposure*30 if exposure else ''}
    for kind, ps in buckets.items():
        active = len({period_start(t, kind) for t in window})
        row['active_' + kind + 's'] = active
        row['observed_' + kind + 's'] = len(ps)
        row['active_' + kind + '_fraction'] = active/len(ps)
        row['mean_events_per_' + kind] = len(window)/len(ps)
    return row


def analyze(events, start, end):
    groups = defaultdict(list)
    for e in events:
        groups[e['contributor_id']].append(e)
    buckets = {kind: periods(start, end, kind) for kind in ('week', 'month')}
    summary = []
    for identity, es in sorted(groups.items()):
        es.sort(key=lambda e: dt(e['timestamp']))
        row = {k: es[-1][k] for k in ('contributor_id', 'login', 'identity_status')}
        row['bot_candidate'] = any(e['bot_candidate'] for e in es)
        for activity in ('all',) + TYPES:
            times = sorted(dt(e['timestamp']) for e in es
                           if activity == 'all' or e['activity_type'] == activity)
            prefix = '' if activity == 'all' else activity + '_'
            row.update({prefix+k: v for k, v in metrics(times, start, end, buckets).items()})
        summary.append(row)
    def detail(kind):
        for identity, es in sorted(groups.items()):
            by_period = defaultdict(list)
            for e in es:
                t = dt(e['timestamp'])
                if start <= t < end:
                    by_period[period_start(t, kind)].append(e)
            first = dt(es[0]['timestamp'])
            for p, lo, hi in buckets[kind]:
                row = {'contributor_id': identity, 'login': es[-1]['login'],
                       'period_start': p.date().isoformat(), 'observed_start': iso(lo),
                       'observed_end_exclusive': iso(hi),
                       'exposure_days': (hi-lo).total_seconds()/86400,
                       'before_first_observed_activity': hi <= first}
                for activity in ('all',) + TYPES:
                    ts = sorted(dt(e['timestamp']) for e in by_period[p]
                                if activity == 'all' or e['activity_type'] == activity)
                    prefix = '' if activity == 'all' else activity + '_'
                    row[prefix+'count'] = len(ts)
                    row[prefix+'mean_gap_days'] = gap(ts)
                yield row
    return summary, {'week': detail('week'), 'month': detail('month')}


def write_csv(path, rows, empty_fields):
    rows = iter(rows)
    first = next(rows, None)
    temp = path.with_suffix(path.suffix + '.tmp')
    with temp.open('w', newline='', encoding='utf-8-sig') as f:
        writer = csv.DictWriter(f, fieldnames=list(first) if first is not None else empty_fields)
        writer.writeheader()
        if first is not None:
            writer.writerows(chain([first], rows))
    temp.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--repo', default='openai/codex')
    parser.add_argument('--ref', help='Default: repository default branch')
    parser.add_argument('--since', help='Inclusive UTC date/time; default earliest eligible activity')
    parser.add_argument('--until', help='EXCLUSIVE UTC date/time; default snapshot collection start')
    parser.add_argument('--out', type=Path, default=Path('contributor_results'))
    parser.add_argument('--date-field', choices=['author', 'committer'], default='committer')
    parser.add_argument('--exclude-bots', action='store_true')
    parser.add_argument('--exclude-merges', action='store_true')
    parser.add_argument('--recover-openings-since',
                        help='Fetch issues/PRs updated since this UTC date, newest first; '
                             'merge with old cache and regenerate all CSVs.')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', args.repo):
        parser.error('--repo must be owner/repo')
    # Validate explicit dates before issuing requests.
    recovery_start = dt(args.recover_openings_since) if args.recover_openings_since else None
    requested_start = dt(args.since) if args.since else None
    requested_end = dt(args.until) if args.until else None
    if requested_start and requested_end and requested_start >= requested_end:
        parser.error('--since must precede --until')
    cache = args.out / 'cache'
    cache.mkdir(parents=True, exist_ok=True)
    state, commits = collect(args, cache)
    end = requested_end or dt(state['collection_started_at'])
    if end > dt(state['collection_started_at']):
        raise ValueError('--until exceeds snapshot collection time; choose an earlier end or a new --out.')
    openings = collect_openings(args, cache, dt(state['collection_started_at']))
    if recovery_start:
        if recovery_start >= end:
            raise ValueError('--recover-openings-since must precede --until.')
        recovered = collect_openings(args, cache, dt(state['collection_started_at']),
                                     updated_since=recovery_start)
        merged = {item['id']: item for item in openings}
        before = len(merged)
        merged.update({item['id']: item for item in recovered})
        openings = list(merged.values())
        print(f'Recovery added {len(merged)-before} unique openings; '
              'overlapping records were deduplicated.', flush=True)
        # Persist supplements, so a later run without the recovery flag retains them.
        save_json(cache / 'recovered_openings.json', {
            'items': openings, 'updated_since': iso(recovery_start),
            'recorded_at': iso(datetime.now(UTC))})
    supplement = cache / 'recovered_openings.json'
    if supplement.exists():
        merged = {item['id']: item for item in openings}
        merged.update({item['id']: item for item in json.loads(supplement.read_text())['items']})
        openings = list(merged.values())
    events = normalize(commits, openings, args, end)
    if not events:
        raise ValueError('No eligible activities before --until; no result CSVs written.')
    start = requested_start or dt(events[0]['timestamp']).replace(hour=0, minute=0, second=0, microsecond=0)
    if start >= end:
        raise ValueError('--since must precede --until')
    summary, detailed = analyze(events, start, end)
    if recovery_start:
        backup = args.out / ('before_recovery_' + datetime.now(UTC).strftime('%Y%m%dT%H%M%S%fZ'))
        backup.mkdir()
        for name in ('contributors.csv', 'weekly.csv', 'monthly.csv', 'events.csv',
                     'commits.csv', 'methodology.json'):
            old = args.out / name
            if old.exists():
                shutil.copy2(old, backup / name)
        print(f'Previous outputs backed up in {backup}', flush=True)
    write_csv(args.out/'contributors.csv', summary, ['contributor_id'])
    write_csv(args.out/'weekly.csv', detailed['week'], ['contributor_id', 'period_start'])
    write_csv(args.out/'monthly.csv', detailed['month'], ['contributor_id', 'period_start'])
    for e in events:
        e['in_observation_window'] = start <= dt(e['timestamp']) < end
    write_csv(args.out/'events.csv', events, ['event_id'])
    write_csv(args.out/'commits.csv', (e for e in events if e['activity_type'] == 'commit'), list(events[0]))
    save_json(args.out/'methodology.json', {**state, 'since_inclusive': iso(start),
        'until_exclusive': iso(end), 'timestamp_field': args.date_field,
        'exclude_bots': args.exclude_bots, 'exclude_merges': args.exclude_merges,
        'fetched_unique_commits': len(commits), 'fetched_openings': len(openings),
        'eligible_historical_events': {t: sum(e['activity_type'] == t for e in events) for t in TYPES},
        'script_version': 4,
        'recovery_used': supplement.exists(),
        'identities': len(summary), 'definitions_and_limitations': __doc__})
    for activity in TYPES:
        dates = [e['timestamp'] for e in events if e['activity_type'] == activity]
        print(f'{activity}: {len(dates)} events; latest: {max(dates) if dates else "none"}')
    print(f'Done: {len(summary)} contributor identities. CSVs in {args.out.resolve()}')


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        sys.exit('\nInterrupted; cached pages retained. Rerun to resume.')
    except (ValueError, RuntimeError, OSError) as exc:
        sys.exit(str(exc))
