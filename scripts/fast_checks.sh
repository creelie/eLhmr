#!/usr/bin/env bash
# fast_checks.sh -- re-run the quicker programs and compare their output with
# the recorded logs, ignoring timings. About 15 minutes on one core.
#
#   scripts/fast_checks.sh [OUTDIR]     (default build/fast-checks)
#
# Needs Python 3 with sympy, numpy, gmpy2 and python-flint, and PARI/GP.
# The long searches (the case k = 15, the eight-prime search, the independent
# sets of Proposition 2.5) are not re-run here; their logs are in logs/,
# data/ and bound/logs/, and README.md says how to repeat them.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$ROOT/build/fast-checks}"
mkdir -p "$OUT"
cd "$ROOT"

# drop colour codes, blank lines, the output of `time` and every timing
norm() {
  sed -E 's/\x1b\[[0-9;]*m//g' "$1" \
    | grep -vE '^(real|user|sys)[[:space:]]|^[[:space:]]*$' \
    | sed -E 's/[0-9]+(\.[0-9]+)? ?(s|min)\b//g'
}

fail=0
check() {
  local name=$1 recorded=$2; shift 2
  local start=$SECONDS
  if ! "$@" > "$OUT/$name.log" 2>&1; then
    echo "FAIL  $name: exit status $?"; fail=1; return
  fi
  if diff <(norm "$recorded") <(norm "$OUT/$name.log") > "$OUT/$name.diff"; then
    echo "ok    $name ($((SECONDS - start)) s)"
    rm -f "$OUT/$name.diff"
  else
    echo "FAIL  $name: output differs from $recorded"; head -20 "$OUT/$name.diff"; fail=1
  fi
}

gp_search() { ( cd bound && printf 's = 7;\n\\r search.gp\n' | gp -q -D debugmem=0 ); }

check thresholds              logs/thresholds.log              python3 thresholds.py
check extensions              logs/extensions.log              python3 extensions.py
check check_certificates      logs/check_certificates.log      python3 check_certificates.py
check hand_bound              bound/logs/hand_bound.log        python3 bound/hand_bound.py
check ratio_bound             bound/logs/ratio_bound.log       python3 bound/ratio_bound.py 16000
check search_py_s7            bound/logs/search_py_s7.log      python3 bound/search.py 7
check search_gp_s7            bound/logs/search_gp_s7.log      gp_search
check validate_lastthree      logs/validate_lastthree.log      python3 tests/validate_lastthree.py
check validate_b              logs/validate_b.log              python3 tests/validate_b.py
check validate_c              logs/validate_c.log              python3 tests/validate_c.py
check lattice_finds_solutions logs/lattice_finds_solutions.log python3 tests/lattice_finds_solutions.py
check compare_runs            logs/compare_runs.log            python3 tests/compare_runs.py
check walls                   logs/walls.log                   python3 walls.py
check second_equation         logs/second_equation.log         python3 second_equation.py
check first_equation          logs/first_equation.log          python3 first_equation.py

if [ "$fail" -ne 0 ]; then
  echo "fast_checks.sh: some checks failed (logs in $OUT)" >&2
  exit 1
fi
echo "all checks agree with the recorded logs"
