#/bin/bash

ARTIFACT_ID=$1

echo "Unpacking ZIP."
unzip -o tmp/artifact_${ARTIFACT_ID}.zip -d tmp/artifact_${ARTIFACT_ID}
echo "Unpacking TAR."
for f in tmp/artifact_${ARTIFACT_ID}/* #Should only be one file
do
  echo "Unpacking $f"
  mkdir tmp/artifact_${ARTIFACT_ID}_inner
  tar -xvf $f -C tmp/artifact_${ARTIFACT_ID}_inner
done
