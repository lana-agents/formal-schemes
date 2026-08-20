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
lake exe mk_all --lib FormalSchemes --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
