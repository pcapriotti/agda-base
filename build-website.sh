#!/bin/bash -e

if [ "${TRAVIS_PULL_REQUEST}" = "false" ];
then
  # generate html
  html=`mktemp -d`
  sha=`git log -1 HEAD --pretty=format:%H`
  agda -i. --html --html-dir=$html README.agda
  mv $html/README.html $html/index.html

  # commit
  cd $html
  git init
  git config user.name "Paolo Capriotti"
  git config user.email "paolo@capriotti.io"
  git remote add origin https://$GIT_TOKEN@github.com/pcapriotti/agda-base
  git fetch origin
  git reset origin/gh-pages
  git add -A
  git commit -m "Update: $sha" || true
  git push origin master:gh-pages 2>/dev/null || ( echo "Could not push" && false )

  # cleanup
  cd -
  rm -fr $html
else
  echo "pull request, skipping website generation"
fi
