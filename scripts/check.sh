#!/usr/bin/env bash
# Every offline suite, in one run: no TypeDB server, real Lean 4.
#
#   scripts/check.sh
#
# Exit codes, distinct on purpose:
#   0  every stage passed
#   1  a real failure
#   2  the environment is broken (no Lean, no driver)
#   3  a stage could not judge (the infrastructure failed, not the system)
set -uo pipefail
cd "$(dirname "$0")/.."
PY="${PYTHON:-python3}"

command -v lean >/dev/null || { echo "lean not on PATH"; exit 2; }
"$PY" -c "import typedb.driver" 2>/dev/null \
  || { echo "typedb-driver not installed for $PY"; exit 2; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
FAILED=()
NOT_JUDGED=()
STAGE=0

stage() {                                   # stage "<name>" <command...>
  STAGE=$((STAGE + 1))
  local name="$1"; shift
  printf '\n━━━ %d. %s\n' "$STAGE" "$name"
  if "$@" > "$WORK/$STAGE.log" 2>&1; then
    tail -n "${TAIL:-2}" "$WORK/$STAGE.log" | sed 's/^/    /'
    echo "    → pass"
  else
    local code=$?
    tail -n 25 "$WORK/$STAGE.log" | sed 's/^/    /'
    if [ "$code" = 3 ]; then
      echo "    → NOT JUDGED"
      NOT_JUDGED+=("$STAGE. $name")
    else
      echo "    → FAIL (exit $code)"
      FAILED+=("$STAGE. $name")
    fi
  fi
}

# ── the core, and the trust boundary ─────────────────────────────────
stage "core" "$PY" tests/test_core.py
stage "type bridge, attack tests" "$PY" tests/test_bridge.py
stage "the kernel's verdict" "$PY" tests/test_kernel_decision.py
stage "acceptor arithmetic" "$PY" tests/test_acceptor.py

# ── pinned outputs and the search ────────────────────────────────────
search_suites() {
  "$PY" tests/golden.py || return 1
  "$PY" tests/golden_props.py || return 1
  "$PY" tests/test_search_props.py || return 1
  "$PY" tests/test_search_world.py || return 1
  "$PY" tests/test_search_generators.py || return 1
  "$PY" tests/test_search_pipeline.py || return 1
  "$PY" tests/test_counterexamples.py || return 1
  "$PY" tests/make_counterexamples.py || return 1
}
TAIL=8 stage "golden pins and the search suites" search_suites

# ── against real Lean ────────────────────────────────────────────────
stage "fixture rules vs Lean" "$PY" tests/test_lean_offline.py
stage "acceptor against real Lean" "$PY" tests/test_acceptor_live.py

# ── does the suite have teeth? ───────────────────────────────────────
TAIL=3 stage "deliberate defects, each caught by its own suite" \
  "$PY" tests/test_mutation.py

echo
if [ ${#FAILED[@]} -gt 0 ]; then
  printf 'FAILED:\n'; printf '  %s\n' "${FAILED[@]}"; exit 1
fi
if [ ${#NOT_JUDGED[@]} -gt 0 ]; then
  printf 'NOT JUDGED:\n'; printf '  %s\n' "${NOT_JUDGED[@]}"; exit 3
fi
echo "all $STAGE stages passed"
