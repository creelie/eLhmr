#!/usr/bin/env bash
# build_journal.sh -- build the journal version of the paper (paper/journal.tex,
# the results of paper/main.tex without Section 9 and the appendices, which
# stay in this archive) and its source package into dist/:
#
#   dist/lehmer-totient-journal.pdf      the compiled manuscript
#   dist/lehmer-totient-journal-tex.zip  journal.tex with the figures it uses
#                                        as PNG, compiling on its own
#
# Needs pdflatex with amsart and the fonts of paper/main.tex, and zip.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/paper"
DIST="$ROOT/dist"
NAME=lehmer-totient-journal
mkdir -p "$DIST"

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }
latex3() { latex "$@" && latex "$@" && latex "$@"; }
check_log() {
  if grep -q "Overfull\|undefined\|multiply defined" "$1"; then
    grep "Overfull\|undefined\|multiply defined" "$1"
    echo "build_journal.sh: fix the warnings above ($1)" >&2
    exit 1
  fi
}

cd "$PAPER"
FIGS=$(grep -o 'figures/fig_[a-z0-9]*\.png' journal.tex | sed 's#figures/##; s#\.png$##' | sort -u)
rm -f journal.aux journal.out
latex3 journal.tex
check_log journal.log
cp journal.pdf "$DIST/$NAME.pdf"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
mkdir -p "$STAGE/$NAME/figures"
cp journal.tex "$STAGE/$NAME/"
for f in $FIGS; do cp "figures/$f.png" "$STAGE/$NAME/figures/"; done
( cd "$STAGE/$NAME" && latex3 journal.tex && check_log journal.log \
  && rm -f journal.aux journal.log journal.out journal.pdf )
rm -f "$DIST/$NAME-tex.zip"
( cd "$STAGE" && zip -qr "$DIST/$NAME-tex.zip" "$NAME" )

rm -f journal.aux journal.log journal.out journal.pdf
echo "$(echo "$FIGS" | wc -w) figures"
ls -l "$DIST/$NAME.pdf" "$DIST/$NAME-tex.zip"
