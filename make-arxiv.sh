#!/usr/bin/env bash
# Package the paper for arXiv, with the Lean project as ancillary files.
#
#   ./make-arxiv.sh [-o OUT.tar.gz] [--no-check]
#
# Layout of the tarball (arXiv takes ancillary files from a top-level anc/):
#
#   main.tex  main.bbl  macros.tex  refs.bib  sections/*.tex
#   anc/README.md                  the project README
#   anc/lean/...                   the Lake project, without .lake/ and build outputs
#
# arXiv does not run BibTeX, so main.bbl is shipped and must be current (the check below catches
# a citation missing from it); the PDF and the other LaTeX outputs are left out. The sources in
# this directory are not modified: if main.tex has no \pdfoutput=1 in its first five lines, the
# line is added to the copy in the tarball only, so that arXiv compiles with pdflatex as we do.
#
# Unless --no-check is given, the staged copy is compiled exactly as arXiv does (pdflatex, no
# BibTeX, twice) and the script fails on LaTeX errors or undefined references and citations.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PAPER="$ROOT/paper/kmrr-solutions"
LEAN="$ROOT/lean"
OUT="$ROOT/arxiv-submission.tar.gz"
CHECK=1

while [ $# -gt 0 ]; do
  case "$1" in
    -o) OUT="$(realpath -m "$2")"; shift 2 ;;
    --no-check) CHECK=0; shift ;;
    -h|--help) awk 'NR > 1 && !/^#/ { exit } NR > 1 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

die() { echo "error: $*" >&2; exit 1; }

[ -f "$PAPER/main.tex" ] || die "missing $PAPER/main.tex"
[ -f "$PAPER/main.bbl" ] || die "missing $PAPER/main.bbl (arXiv does not run BibTeX)"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
PKG="$STAGE/pkg"
mkdir -p "$PKG/sections" "$PKG/anc/lean"

# --- paper: sources only
cp "$PAPER/main.tex" "$PAPER/main.bbl" "$PAPER/macros.tex" "$PAPER/refs.bib" "$PKG/"
cp "$PAPER"/sections/*.tex "$PKG/sections/"
if ! head -n 5 "$PKG/main.tex" | grep -q '\\pdfoutput=1'; then
  { printf '%s\n' '\pdfoutput=1'; cat "$PAPER/main.tex"; } > "$PKG/main.tex"
  echo "note: added \\pdfoutput=1 to the packaged main.tex"
fi

# --- Lean project: sources and Lake configuration, no build outputs, no dotfiles
cp "$ROOT/README.md" "$PKG/anc/README.md"
( cd "$LEAN" && find . \( -name .lake -o -name build -o -name lake-packages -o -name '.*' ! -name . \) -prune \
    -o -type f -print ) | while read -r f; do
  mkdir -p "$PKG/anc/lean/$(dirname "$f")"
  cp "$LEAN/$f" "$PKG/anc/lean/$f"
done
[ -f "$PKG/anc/lean/lakefile.toml" ] || die "Lean project not found under $LEAN"

# --- arXiv accepts only these characters in file names
bad="$(cd "$PKG" && find . -type f | sed 's|^\./||' | grep -v '^[A-Za-z0-9_+.,=/-]*$' || true)"
[ -z "$bad" ] || die "file names arXiv will reject:"$'\n'"$bad"

# --- compile the staged copy the way arXiv does
if [ "$CHECK" = 1 ]; then
  command -v pdflatex >/dev/null || die "pdflatex not found (install TeX Live, or pass --no-check)"
  BUILD="$STAGE/build"
  cp -r "$PKG" "$BUILD"
  for pass in 1 2; do
    ( cd "$BUILD" && pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null 2>&1 ) \
      || { tail -n 30 "$BUILD/main.log" >&2; die "pdflatex failed (pass $pass)"; }
  done
  if grep -E 'Warning: (Reference|Citation).*undefined|There were undefined references' "$BUILD/main.log" >&2; then
    die "undefined references or citations"
  fi
  pages="$(grep -o 'Output written on main.pdf ([0-9]* pages' "$BUILD/main.log" | grep -o '[0-9]* pages')"
  echo "check: pdflatex without BibTeX compiles the package, $pages, no undefined references"
fi

# --- reproducible tarball (fixed order, owner and timestamps)
mtime="$(stat -c %Y "$PAPER/main.tex")"
tar -C "$PKG" --sort=name --owner=0 --group=0 --numeric-owner --mtime="@$mtime" -cf - . \
  | gzip -9 -n > "$OUT"

size="$(stat -c %s "$OUT")"
[ "$size" -le $((50 * 1024 * 1024)) ] || echo "warning: $size bytes exceeds arXiv's 50 MB limit" >&2
echo "wrote $OUT ($(tar -tzf "$OUT" | grep -vc '/$') files, $size bytes)"
