#!/bin/bash
set -eo pipefail # Stop on the first failed command, including size checks.

GAMES=$1
ARTIFACT_ID=$2
OWNER=$3
REPO=$4
TEMP="tmp/${OWNER}_${REPO}_${ARTIFACT_ID}"
STAGING="${TEMP}_game"

cd "${GAMES}"

mkdir -p "${OWNER}"
rm -rf "${TEMP}" "${STAGING}"

echo "Unpacking ZIP."
unzip -o "${TEMP}.zip" -d "${TEMP}"
echo "Unpacking game."

# Keep the installed game until extraction and file checks pass.
for f in "${TEMP}"/* #Should only be one file
do
  echo "Unpacking $f"
  unzip -q -o "$f" -d "${STAGING}"
done

for f in .lake/gamedata/game.json lean-toolchain
do
  if [ ! -f "${STAGING}/$f" ]; then
    echo "Imported artifact does not contain $f" >&2
    exit 1
  fi
done

LIMIT_MB=${RESERVED_DISC_SPACE_MB:-0}
if [[ ! "$LIMIT_MB" =~ ^[0-9]+$ ]]; then
  echo "RESERVED_DISC_SPACE_MB must be a non-negative integer" >&2
  exit 1
fi
LIMIT_KB=$((10#$LIMIT_MB * 1024))
if (( LIMIT_KB > 0 )); then
  # Serialize quota checks and replacement across concurrent imports.
  exec 9>tmp/.import.lock
  flock -x 9

  # Temporary downloads and extracted staging directories do not count.
  INSTALLED_KB=$(du -sk --exclude=./tmp . | cut -f1)
  OLD_KB=0
  if [ -d "${OWNER}/${REPO}" ]; then
    OLD_KB=$(du -sk "${OWNER}/${REPO}" | cut -f1)
  fi
  REPLACEMENT_KB=$(du -sk "${STAGING}" | cut -f1)
  FINAL_KB=$((INSTALLED_KB - OLD_KB + REPLACEMENT_KB))
  if (( FINAL_KB > LIMIT_KB )); then
    echo "ABORT IMPORT: Installed games would use $(((FINAL_KB + 1023) / 1024)) MB, exceeding RESERVED_DISC_SPACE_MB=${LIMIT_MB}." >&2
    exit 1
  fi
fi

echo "Replace old version of the game"
rm -rf "${OWNER}/${REPO}"
mv "${STAGING}" "${OWNER}/${REPO}"

# Delete temporary files
rm -f "${TEMP}.zip"
rm -rf "${TEMP}"
