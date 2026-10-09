#!/usr/bin/env bash
set -euo pipefail

# $HOME is read-only in this sandbox, so keep lake's cache dir inside the repo.
export XDG_CACHE_HOME="$PWD/.cache-home"

# Report which commit this build is actually based on. A merger validates the pull
# request branch AS IT IS -- it does not merge master in first -- so a branch cut before
# a fix landed keeps rebuilding the broken tree no matter how often it is retried.
# Printing the base puts that diagnosis in every log instead of leaving it to be
# reconstructed afterwards. Purely informational: never fails the run.
report_base() {
  echo "HEAD:            $(git rev-parse --short HEAD 2>/dev/null || echo '(unknown)')"
  local base
  base="$(git rev-parse --short upstream/master 2>/dev/null || true)"
  if [ -z "$base" ]; then
    echo "upstream/master: (not fetched; base not checked)"
  elif git merge-base --is-ancestor upstream/master HEAD 2>/dev/null; then
    echo "upstream/master: $base -- base is up to date"
  else
    echo "upstream/master: $base -- BASE IS STALE: this build does NOT contain current master"
  fi
}
report_base || true

# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
# `FormalSchemes.lean` starts with a copyright header that mk_all does not write, so regenerate the
# root module with mk_all and compare it with the committed file minus its leading header.
root_saved="$(mktemp)"
cp FormalSchemes.lean "$root_saved"
# mk_all exits 1 when it rewrites the file (always, because of the header); a failed run leaves
# the file with its header, which the comparison below then rejects.
lake exe mk_all --lib FormalSchemes --git > /dev/null || true
if ! awk 'NR == 1 && $0 == "/-" { h = 1 } h { if ($0 == "-/") h = 0; next } { print }' "$root_saved" \
    | cmp -s - FormalSchemes.lean; then
  cp "$root_saved" FormalSchemes.lean
  echo "The file 'FormalSchemes.lean' is out of date: run \`lake exe mk_all --lib FormalSchemes --git\` and keep its header."
  exit 1
fi
cp "$root_saved" FormalSchemes.lean

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
