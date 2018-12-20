#!/bin/bash
set -e

function err() {
    echo "$1" >&2
    exit 1
}

branch="$1"
[ -z "$branch" ] && branch="$CI_COMMIT_REF_NAME"
[ -z "$branch" ] && err "no branch specified"
url="$CI_REPOSITORY_URL"
[ -z "$url" ] && err "no url specified"

# clone pages website
html=public
rm -fr "$html"
git branch -f pages remotes/origin/pages
git clone -b pages . "$html"
rm -fr "$html"/"$branch"

# generate html
agda -i. --html --html-dir="$html"/"$branch" README.agda
mv "$html"/"$branch"/README.html "$html"/"$branch"/index.html

# push updated website
sha=`git log -1 HEAD --pretty=format:%H`
cd "$html"
git add -A
git config user.name "Paolo Capriotti"
git config user.email "paolo@capriotti.io"
git commit -m "Update $branch: $sha" || true

# use appropriate deploy token
url=$(echo "$url" | sed 's|^https://gitlab-ci-token:[^@]*|https://pcapriotti:'"$GITLAB_TOKEN|")

git push "$url" pages:pages

# cleanup
rm -fr .git
