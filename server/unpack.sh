#/bin/bash

ARTIFACT_ID=$1
OWNER=$2
REPO=$3

echo "Creating folders"
cd ..
# mkdir -p games
cd games
pwd
# mkdir -p tmp
mkdir -p ${OWNER}

echo "Unpacking ZIP."
unzip -o tmp/${OWNER}_${REPO}_${ARTIFACT_ID}.zip -d tmp/${OWNER}_${REPO}_${ARTIFACT_ID}
echo "Unpacking game."

# exit the npm project to avoid reloading. TODO: Where should we actually save these?



echo "Delete old version of the game"
rm -rf ${OWNER}/${REPO}
mkdir -p ${OWNER}/${REPO}

for f in tmp/${OWNER}_${REPO}_${ARTIFACT_ID}/* #Should only be one file
do
  echo "Unpacking $f"
  #tar -xvzf $f -C games/${OWNER}/${REPO}
  unzip -q -o $f -d ${OWNER}/${REPO}
done
