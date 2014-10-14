#!/bin/bash -e

if [ "${TRAVIS_PULL_REQUEST}" = "false" ]
then
  if [ "$#" -gt 0 ]
  then
    branch="$1"
  else
    branch="$(git rev-parse --abbrev-ref HEAD)"
  fi
  html=`mktemp -d`

  # setup repo with gh-pages branch
  git clone -b gh-pages https://$GIT_TOKEN@github.com/pcapriotti/agda-base $html
  cd $html
  git config user.name "Paolo Capriotti"
  git config user.email "paolo@capriotti.io"
  rm -fr "$branch"
  cd -

  # generate html
  agda -i. --html --html-dir=$html/$branch README.agda
  mv $html/$branch/README.html $html/$branch/index.html

  # commit
  sha=`git log -1 HEAD --pretty=format:%H`
  cd $html
  git add -A
  git commit -m "Update $branch: $sha" || true
  git push origin 2>/dev/null || ( echo "Could not push" && false )

  # cleanup
  cd -
  rm -fr $html
else
  echo "skipping website generation"
fi
