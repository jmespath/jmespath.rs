#!/bin/bash
set -e

# Don't build for non-master or for PRs
[ "${TRAVIS_BRANCH}" != 'master' ] && exit 0
[ "${TRAVIS_PULL_REQUEST}" = 'true' ] && exit 0

# Fail if require environment variables are not found.
[ -z "${GH_TOKEN}" ] && exit 1
[ -z "${TRAVIS_REPO_SLUG}" ] && exit 2

# Clear out and regenerate documentation.
rm -rf target/doc
cargo doc
cd target/doc

uri="https://${GH_TOKEN}@github.com/${TRAVIS_REPO_SLUG}"
git init
git config user.name "Travis-CI"
git config user.email "builder@travis"
git add .
git commit -m "Deploy to Github Pages"
git push --force --quiet "${uri}" master:gh-pages > /dev/null 2>&1
