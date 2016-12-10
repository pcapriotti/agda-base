#!/bin/bash
set -e

branch="$1"
[ -z "$branch" ] && branch="$CI_BUILD_REF_NAME"

# clone pages website
html=public
git clone -b pages . "$html"
rm -fr "$html"/"$branch"

# generate html
agda -i. --html --html-dir="$html"/"$branch" README.agda
mv "$html"/"$branch"/README.html "$html"/"$branch"/index.html

# push updated website
cd "$html"
git add -A
git commit -m "Update $branch: $CI_BUILD_REF" || true
git push origin
