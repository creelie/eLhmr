#!/usr/bin/env bash
# build_submission.sh -- the files for a submission to the Journal of Number
# Theory, in build/submission/ (not committed):
#
#   lehmer-totient.pdf           the compiled manuscript
#   lehmer-totient-source.zip    main.tex with the figures named Fig1, ...,
#                                Fig21 in the order in which they appear, as
#                                PDF (used by pdflatex) and EPS (vector artwork)
#
# Runs scripts/build_paper.sh first. Needs pdftops (poppler) for the EPS files.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NAME=lehmer-totient
OUT="$ROOT/build/submission"
"$ROOT/scripts/build_paper.sh" > /dev/null

rm -rf "$OUT"
mkdir -p "$OUT/src"
cd "$ROOT/paper"
cp main.tex "$OUT/src/main.tex"
i=0
for f in $(grep -o 'figures/fig_[a-z0-9]*\.png' main.tex | sed 's#figures/##; s#\.png$##' | awk '!seen[$0]++'); do
  i=$((i + 1))
  sed -i "s#{figures/$f\.png}#{Fig$i}#" "$OUT/src/main.tex"
  cp "figures/build/$f.pdf" "$OUT/src/Fig$i.pdf"
  pdftops -eps "figures/build/$f.pdf" "$OUT/src/Fig$i.eps"
done
if grep -q '{figures/' "$OUT/src/main.tex"; then
  echo "build_submission.sh: a figure was not renamed" >&2
  exit 1
fi

# the zipped source must compile on its own
( cd "$OUT/src" \
  && for k in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error main.tex > /dev/null; done \
  && ! grep -q "Overfull\|undefined" main.log \
  && rm -f main.aux main.log main.out main.pdf )
( cd "$OUT/src" && zip -q "$OUT/$NAME-source.zip" main.tex Fig*.pdf Fig*.eps )
rm -rf "$OUT/src"
cp "$ROOT/dist/$NAME.pdf" "$OUT/"
echo "$i figures"
ls -l "$OUT"
