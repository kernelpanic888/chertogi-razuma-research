#!/bin/sh
set -eu

TOKEN_FILE="${COUNTER_TOKEN_FILE:-/Users/test/Documents/Codex/.secrets/chertogi-counter-read-token}"
SITE_URL="https://chertogi-razuma-research.kernelpanic888.chatgpt.site"

if [ ! -r "$TOKEN_FILE" ]; then
  printf 'Counter token is unavailable: %s\n' "$TOKEN_FILE" >&2
  exit 1
fi

/usr/bin/curl \
  --fail-with-body \
  --silent \
  --show-error \
  --header "Authorization: Bearer $(/bin/cat "$TOKEN_FILE")" \
  "$SITE_URL/_internal/page-views"
printf '\n'
