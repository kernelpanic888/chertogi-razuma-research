#!/bin/sh
set -eu

TOKEN_FILE="${COUNTER_TOKEN_FILE:-/Users/test/Documents/Codex/.secrets/chertogi-counter-read-token}"
SITE_URL="https://chertogi-razuma-research.kernelpanic888.chatgpt.site"
MAX_ATTEMPTS="${COUNTER_READ_ATTEMPTS:-2}"

case "$MAX_ATTEMPTS" in
  1|2|3) ;;
  *) MAX_ATTEMPTS=3 ;;
esac

if [ ! -r "$TOKEN_FILE" ]; then
  printf 'Counter token is unavailable: %s\n' "$TOKEN_FILE" >&2
  exit 1
fi

if ! TOKEN=$(/bin/cat "$TOKEN_FILE" 2>/dev/null) || [ -z "$TOKEN" ]; then
  printf 'Counter credential could not be loaded\n' >&2
  exit 1
fi

run_with_timeout() {
  /usr/bin/perl -e '
    my $seconds = shift @ARGV;
    my $pid = fork();
    exit 125 unless defined $pid;
    if ($pid == 0) {
      exec @ARGV;
      exit 126;
    }
    local $SIG{ALRM} = sub {
      kill "TERM", $pid;
      select undef, undef, undef, 0.2;
      kill "KILL", $pid;
      waitpid $pid, 0;
      exit 124;
    };
    alarm $seconds;
    waitpid $pid, 0;
    alarm 0;
    exit ($? >> 8);
  ' 12 "$@"
}

attempt=1
while [ "$attempt" -le "$MAX_ATTEMPTS" ]; do
  response=""
  if response=$(run_with_timeout /usr/bin/curl \
    --fail-with-body \
    --silent \
    --connect-timeout 3 \
    --max-time 10 \
    --header "Authorization: Bearer $TOKEN" \
    "$SITE_URL/_internal/page-views" 2>/dev/null); then
    value=$(printf '%s' "$response" | /usr/bin/sed -nE \
      's/^[[:space:]]*\{"page_views":[[:space:]]*([0-9]+)\}[[:space:]]*$/\1/p')
    if [ -n "$value" ]; then
      printf '{"page_views":%s}\n' "$value"
      exit 0
    fi
  fi

  if [ "$attempt" -lt "$MAX_ATTEMPTS" ]; then
    /bin/sleep 2
  fi
  attempt=$((attempt + 1))
done

printf 'Counter read failed: no valid response after %s attempts\n' "$MAX_ATTEMPTS" >&2
exit 1
