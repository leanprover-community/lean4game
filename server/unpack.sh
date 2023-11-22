#/bin/bash

ARTIFACT_ID=$1
OWNER=$2
REPO=$3

echo "Unpacking ZIP."
# unzip -o games/tmp/${OWNER}_${REPO}_${ARTIFACT_ID}.zip -d games/tmp/${OWNER}_${REPO}_${ARTIFACT_ID}
echo "Unpacking game."
rm -rf games/${OWNER}/${REPO}
mkdir games/${OWNER}/${REPO}

for f in games/tmp/${OWNER}_${REPO}_${ARTIFACT_ID}/* #Should only be one file
do
  echo "Unpacking $f"
  #tar -xvzf $f -C games/${OWNER}/${REPO}
  mkdir games/${OWNER}/${REPO}
  unzip -o $f -d games/${OWNER}/${REPO}
done
