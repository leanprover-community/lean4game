#/bin/bash

GAMES=$1
ARTIFACT_ID=$2
OWNER=$3
REPO=$4

# mkdir -p games
cd ${GAMES}

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

# Delete temporary files
rm -f tmp/${OWNER}_${REPO}_${ARTIFACT_ID}.zip
rm -fr tmp/${OWNER}_${REPO}_${ARTIFACT_ID}
