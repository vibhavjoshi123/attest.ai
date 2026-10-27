#!/usr/bin/env bash
# The two example domains, end to end against a real TypeDB 3 server and a
# real Lean 4. Nothing is mocked.
#
#   scripts/examples.sh
#
# Needs: Lean 4 on PATH, `typedb-driver` installed, and a reachable server
# (TYPEDB_ADDRESS, TYPEDB_USERNAME, TYPEDB_PASSWORD; TYPEDB_TLS=1 for TLS).
#
# Exit codes: 0 every stage passed · 1 a real failure · 2 the environment is
# broken · 3 the server could not be reached, so nothing was judged.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
PY="${PYTHON:-python3}"

command -v lean >/dev/null || { echo "lean not on PATH"; exit 2; }
"$PY" -c "import typedb.driver" 2>/dev/null \
  || { echo "typedb-driver not installed for $PY"; exit 2; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
FAILED=()
NOT_JUDGED=()
STAGE=0
UNREACHABLE='connection error|Unable to connect|CXN0|transport error'

stage() {                                   # stage "<name>" <command...>
  STAGE=$((STAGE + 1))
  local name="$1"; shift
  printf '\n━━━ %d. %s\n' "$STAGE" "$name"
  if "$@" > "$WORK/$STAGE.log" 2>&1; then
    tail -n 3 "$WORK/$STAGE.log" | sed 's/^/    /'
    echo "    → pass"
  else
    local code=$?
    tail -n 25 "$WORK/$STAGE.log" | sed 's/^/    /'
    if [ "$code" = 3 ] || grep -qEi "$UNREACHABLE" "$WORK/$STAGE.log"; then
      echo "    → NOT JUDGED (the server, not the system)"
      NOT_JUDGED+=("$STAGE. $name")
    else
      echo "    → FAIL (exit $code)"
      FAILED+=("$STAGE. $name")
    fi
  fi
}

# Parameters, scoped closures, double-negation reliance, a rule over global
# facts, and an axiom-free recheck. The runner asserts every outcome.
scoping() { PYTHONPATH="$ROOT" "$PY" examples/scoping/run.py; }
stage "scoping, end to end" scoping

# The sanctions use cases, twice. One run proves the cases; two runs prove
# the trace is reproducible, which is a different property: a hash that
# varies between identical runs is not a certificate.
sanctions() { PYTHONPATH="$ROOT" "$PY" examples/sanctions/run.py; }
stage "sanctions, end to end (run A)" sanctions
cp examples/sanctions/trace.json "$WORK/trace-A.json" 2>/dev/null || true
stage "sanctions, end to end (run B)" sanctions
reproducible() {
  [ -f "$WORK/trace-A.json" ] || { echo "run A wrote no trace"; return 3; }
  diff -u "$WORK/trace-A.json" examples/sanctions/trace.json \
    && echo "the trace is byte-identical across two live runs"
}
stage "the sanctions trace is reproducible" reproducible

echo
if [ ${#FAILED[@]} -gt 0 ]; then
  printf 'FAILED:\n'; printf '  %s\n' "${FAILED[@]}"; exit 1
fi
if [ ${#NOT_JUDGED[@]} -gt 0 ]; then
  printf 'NOT JUDGED:\n'; printf '  %s\n' "${NOT_JUDGED[@]}"; exit 3
fi
echo "all $STAGE stages passed"
