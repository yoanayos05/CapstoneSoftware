import csv
import hashlib
import json
import subprocess
import time
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urlencode, quote

ROOT = Path.cwd()
CACHE = ROOT / "raw"
CACHE.mkdir(exist_ok=True)

START = datetime(2025, 10, 22, tzinfo=timezone.utc)
END = datetime(2026, 10, 21, tzinfo=timezone.utc)

REPO = "repos/openai/codex"

# Add accounts here only after recording supporting evidence.
CONFIRMED_BOTS = {"github-actions[bot]"}
# Conservative account-level flag, not proof every event is automated.
MIXED_ACCOUNTS = {"dabazti"}

def stamp(dt):
    return dt.strftime("%Y-%m-%dT%H:%M:%SZ")

def parse(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00"))

def api(path, **params):
    endpoint = path + ("?" + urlencode(params) if params else "")
    key = hashlib.sha256(endpoint.encode()).hexdigest()
    cached = CACHE / (key + ".json")

    if cached.exists():
        return json.loads(cached.read_text())

    for attempt in range(5):
        result = subprocess.run(
            ["gh", "api", endpoint],
            text=True,
            capture_output=True
        )

        if result.returncode == 0:
            break

        message = result.stderr.lower()
        temporary_error = any(text in message for text in (
            "connection reset",
            "timeout",
            "timed out",
            "unexpected eof",
            "stream error",
            "http 502",
            "http 503",
            "http 504",
        ))

        if not temporary_error or attempt == 4:
            raise RuntimeError(
                "API request failed. Cached pages are saved.\n"
                + result.stderr
            )

        delay = 5 * (2 ** attempt)
        print(
            f"Temporary connection error. Retrying in {delay} seconds...",
            flush=True
        )
        time.sleep(delay)

    data = json.loads(result.stdout)
    cached.write_text(json.dumps(data))

    with (ROOT / "requests.jsonl").open("a") as f:
        f.write(json.dumps({
            "endpoint": endpoint,
            "retrieved_at": stamp(datetime.now(timezone.utc)),
            "cache_file": cached.name
        }) + "\n")

    return data

def classification(user):
    user = user or {}
    login = user.get("login", "").lower()
    if user.get("type") == "Bot" or login in CONFIRMED_BOTS:
        return "confirmed_bot"
    if login in MIXED_ACCOUNTS:
        return "flagged_mixed"
    if not login or user.get("type") != "User":
        return "unknown"
    return "remaining"

def write_csv(name, rows, fields):
    with (ROOT / name).open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)

events = {}

def add_event(kind, identifier, date, user, url):
    dt = parse(date)
    if not START <= dt < END:
        return
    user = user or {}
    events[(kind, str(identifier))] = {
        "activity": kind,
        "event_id": str(identifier),
        "date": date,
        "login": user.get("login", ""),
        "account_id": user.get("id", ""),
        "account_type": user.get("type", ""),
        "classification": (
            "automation" if kind == "workflow_run"
            else classification(user)
        ),
        "url": url
    }

print("Collecting issues and PRs...", flush=True)

endpoint = REPO + "/issues?" + urlencode({
    "state": "all",
    "sort": "created",
    "direction": "asc",
    "since": stamp(START - timedelta(seconds=1)),
    "per_page": 100
})

# No numbered "page" parameter: gh follows next-page links.
key = hashlib.sha256(endpoint.encode()).hexdigest()
issues_file = CACHE / ("issues_paginated_" + key + ".json")

if not issues_file.exists():
    temporary = issues_file.with_suffix(".partial")

    print("Downloading all issue/PR pages; this may take several minutes.",
          flush=True)

    with temporary.open("w") as output:
        result = subprocess.run(
            ["gh", "api", "--paginate", "--slurp", endpoint],
            stdout=output,
            stderr=subprocess.PIPE,
            text=True
        )

    if result.returncode:
        raise RuntimeError(
            "Issue/PR download failed. Do not use the partial file.\n"
            + result.stderr
        )

    # Verify the complete output before marking it as ready.
    with temporary.open() as f:
        pages = json.load(f)

    if not isinstance(pages, list) or any(
        not isinstance(page, list) for page in pages
    ):
        raise RuntimeError("Unexpected issue/PR response format.")

    temporary.replace(issues_file)

    with (ROOT / "requests.jsonl").open("a") as f:
        f.write(json.dumps({
            "endpoint": endpoint,
            "pagination": "gh --paginate --slurp",
            "retrieved_at": stamp(datetime.now(timezone.utc)),
            "cache_file": issues_file.name
        }) + "\n")

with issues_file.open() as f:
    pages = json.load(f)

for batch in pages:
    for item in batch:
        kind = "pull_request" if "pull_request" in item else "issue"
        add_event(
            kind,
            item["number"],
            item["created_at"],
            item.get("user"),
            item["html_url"]
        )

print("Issue/PR collection complete.", flush=True)

print("Pinning default-branch snapshot...", flush=True)
repository = api(REPO)
branch = repository["default_branch"]
tip = api(REPO + "/commits/" + quote(branch, safe=""))["sha"]

(ROOT / "scope.json").write_text(json.dumps({
    "repository": "openai/codex",
    "start_inclusive": stamp(START),
    "end_exclusive": stamp(END),
    "commit_branch": branch,
    "commit_snapshot": tip,
    "commit_date_field": "commit.committer.date",
    "commit_account_field": "author",
    "merge_commits": "included",
    "workflow_reruns": "one event per distinct run ID",
    "confirmed_bot_logins": sorted(CONFIRMED_BOTS),
    "flagged_mixed_logins": sorted(MIXED_ACCOUNTS)
}, indent=2))

print("Collecting commits...", flush=True)
page = 1
while True:
    batch = api(
        REPO + "/commits",
        sha=tip, since=stamp(START - timedelta(seconds=1)),
        until=stamp(END), per_page=100, page=page
    )
    if not batch:
        break
    for item in batch:
        add_event(
            "commit", item["sha"],
            item["commit"]["committer"]["date"],
            item.get("author"), item["html_url"]
        )
    print("  Commit page", page, flush=True)
    page += 1

def collect_runs(left, right):
    # API ranges are inclusive; our analysis interval is half-open.
    interval = stamp(left) + ".." + stamp(right - timedelta(seconds=1))
    first = api(
        REPO + "/actions/runs",
        created=interval, per_page=100, page=1
    )
    count = first["total_count"]

    # Split intervals that exceed the filtered-search limit.
    if count > 1000:
        seconds = int((right - left).total_seconds())
        if seconds <= 1:
            raise RuntimeError("Too many workflow runs in one second.")
        middle = left + timedelta(seconds=seconds // 2)
        collect_runs(left, middle)
        collect_runs(middle, right)
        return

    runs = {r["id"]: r for r in first["workflow_runs"]}
    for page in range(2, (count + 99) // 100 + 1):
        batch = api(
            REPO + "/actions/runs",
            created=interval, per_page=100, page=page
        )
        runs.update({r["id"]: r for r in batch["workflow_runs"]})

    if len(runs) != count:
        raise RuntimeError(
            f"Workflow count mismatch for {interval}: "
            f"expected {count}, retrieved {len(runs)}."
        )

    for run in runs.values():
        add_event(
            "workflow_run", run["id"], run["created_at"],
            run.get("actor"), run["html_url"]
        )

print("Collecting workflow runs...", flush=True)
left = START
while left < END:
    right = min(left + timedelta(days=7), END)
    collect_runs(left, right)
    print("  Workflow interval completed:", stamp(left), flush=True)
    left = right

fields = [
    "activity", "event_id", "date", "login", "account_id",
    "account_type", "classification", "url"
]
rows = sorted(events.values(), key=lambda r: (r["activity"], r["date"]))
write_csv("activity_events.csv", rows, fields)

groups = [
    "confirmed_bot", "flagged_mixed", "unknown",
    "remaining", "automation"
]
kinds = ["commit", "issue", "pull_request", "workflow_run"]
weekly = Counter()
totals = Counter()
accounts = Counter()

for row in rows:
    week = int((parse(row["date"]) - START).total_seconds() // 604800)
    kind, group = row["activity"], row["classification"]
    weekly[(week, kind, group)] += 1
    totals[(kind, group)] += 1
    if kind != "workflow_run":
        accounts[(
            row["login"], row["account_id"],
            row["account_type"], group
        )] += 1

summary = []
for kind in kinds:
    result = {"activity": kind}
    result.update({g: totals[(kind, g)] for g in groups})
    result["total"] = sum(result[g] for g in groups)
    summary.append(result)
    print(kind, result, flush=True)

write_csv("activity_summary.csv", summary, ["activity", "total"] + groups)

weekly_rows = []
for week in range((END - START).days // 7):
    for kind in kinds:
        result = {
            "week_start_utc": stamp(START + timedelta(days=7 * week)),
            "activity": kind
        }
        result.update({g: weekly[(week, kind, g)] for g in groups})
        result["total"] = sum(result[g] for g in groups)
        weekly_rows.append(result)

write_csv(
    "weekly_activity.csv", weekly_rows,
    ["week_start_utc", "activity", "total"] + groups
)

review = [
    dict(zip(
        ["login", "account_id", "account_type", "classification", "events"],
        (*key, count)
    ))
    for key, count in accounts.most_common()
]
write_csv(
    "account_review.csv", review,
    ["login", "account_id", "account_type", "classification", "events"]
)

print("\nDONE. Results saved in:", ROOT)
