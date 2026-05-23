#!/usr/bin/env bash
# scripts/lean-check.sh — fast type-check of a single Lean file.
#
# Strategy:
#  1. Fast path: if the persistent lean-repl daemon (docker compose service
#     `lean-repl`) is running on TCP 127.0.0.1:7878, send the file content
#     and print the JSON response. This is ~5-30 sec/iteration (LSP-equivalent
#     for non-editor authoring).
#  2. Slow fallback: spin up a fresh `verify` container and run
#     `lake env lean <file>`. This is ~5-15 min/iteration (cold Mathlib load
#     every call) — used when the daemon is down.
#
# Bring up the daemon once per session:
#   docker compose -f docker/docker-compose.yml up -d lean-repl
#   docker compose -f docker/docker-compose.yml logs -f lean-repl   # wait for "READY"
# Tear down:
#   docker compose -f docker/docker-compose.yml down lean-repl
#
# Usage:
#   scripts/lean-check.sh HybridVerify/Foundations/BrownianMartingale.lean
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <path-to-lean-file>" >&2
  echo "  e.g. $0 HybridVerify/Foundations/BrownianMartingale.lean" >&2
  exit 2
fi

FILE="$1"
shift || true

if [[ ! -f "$FILE" ]]; then
  echo "[lean-check] file not found: $FILE" >&2
  exit 2
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMPOSE="$REPO_ROOT/docker/docker-compose.yml"
DAEMON_HOST="127.0.0.1"
DAEMON_PORT="7878"

# Fast path: daemon up on 127.0.0.1:7878. Use bash's /dev/tcp to test, then
# pipe the file via `nc` (netcat openbsd flavour: -N closes the write half on
# EOF so the daemon reads to completion).
if exec 3<>/dev/tcp/$DAEMON_HOST/$DAEMON_PORT 2>/dev/null; then
  exec 3>&-
  if command -v ncat >/dev/null 2>&1; then
    ncat --send-only "$DAEMON_HOST" "$DAEMON_PORT" < "$FILE"
  elif nc -h 2>&1 | grep -q -- '-N'; then
    nc -N "$DAEMON_HOST" "$DAEMON_PORT" < "$FILE"
  elif nc -h 2>&1 | grep -q -- '-q'; then
    nc -q 1 "$DAEMON_HOST" "$DAEMON_PORT" < "$FILE"
  else
    # Fallback: pure-bash IO
    exec 4<>/dev/tcp/$DAEMON_HOST/$DAEMON_PORT
    cat "$FILE" >&4
    exec 4>&-  # half-close write, daemon reads EOF
    cat <&4
    exec 4<&-
  fi
  exit 0
fi

# Slow fallback: lake env lean inside a fresh verify container.
echo "[lean-check] daemon not running on $DAEMON_HOST:$DAEMON_PORT — falling back to lake build" >&2
echo "[lean-check] start the daemon for ~30x faster iteration:" >&2
echo "[lean-check]   docker compose -f $COMPOSE up -d lean-repl" >&2

case "$FILE" in
  /app/*) IN_FILE="$FILE" ;;
  *)      IN_FILE="/app/$FILE" ;;
esac

exec docker compose -f "$COMPOSE" run --rm --entrypoint bash verify -c \
  "lake env lean $IN_FILE $* 2>&1"
