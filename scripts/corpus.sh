#!/bin/bash
# Translate each of Bend's proof tests to Lean, check it, and score it against the
# test's own expected verdict:
#   a positive test (Bend accepts it) passes when Lean re-checks every definition;
#   a negative test (expects SOME PROOFS FAIL) passes when Lean rejects it too.
#   BEND_DIR=<bend checkout> LEAN=<lean binary> scripts/corpus.sh > results/corpus.tsv
ROOT=$(cd "$(dirname "$0")/.." && pwd)
LEAN=${LEAN:-lean}
OUT=$(mktemp -d)
cd "${BEND_DIR:?set BEND_DIR to a bend checkout}"
printf "test\texpect\tlean\tclean\tsorry\tskipped\tverdict\n"
for f in tests/proof/*.bend; do
  n=$(basename "$f" .bend)
  if grep -q "^#|SOME PROOFS FAIL" "$f"; then ex=neg; else ex=pos; fi
  timeout 60 bun "$ROOT/bend2lean.ts" "$f" "$OUT/$n.lean" > /dev/null 2> "$OUT/$n.tr"
  if ! grep -q "^translated" "$OUT/$n.tr"; then printf "%s\t%s\t-\t-\t-\t-\t%s\n" "$n" "$ex" "translate-fail"; continue; fi
  skip=$(grep -m1 -o "^translated [0-9]* defs; skipped [0-9]*" "$OUT/$n.tr" | grep -o "[0-9]*$")
  timeout 120 "$LEAN" "$OUT/$n.lean" > "$OUT/$n.log" 2>&1; rc=$?
  ok=$(grep -c "does not depend on any axioms" "$OUT/$n.log"); bad=$(grep -c "sorryAx" "$OUT/$n.log")
  if [ $ex = pos ]; then
    if [ $rc = 0 ] && [ $bad = 0 ] && [ "$skip" = 0 ]; then v=pass; elif [ $rc = 0 ] && [ $bad = 0 ]; then v=partial; else v=fail; fi
  else
    if [ $rc != 0 ] || [ $bad != 0 ]; then v=pass; elif [ "$skip" != 0 ]; then v=partial; else v=ACCEPTED; fi
  fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$n" "$ex" "$rc" "$ok" "$bad" "$skip" "$v"
done
