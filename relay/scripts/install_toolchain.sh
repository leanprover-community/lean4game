GAMES=$1
OWNER=$2
REPO=$3

cd ${GAMES}

echo "Read toolchain."
TOOLCHAIN=$(head ${OWNER}/${REPO}/lean-toolchain)

# Check without installing; games can share a toolchain.
if elan run "${TOOLCHAIN}" lean --version > /dev/null 2>&1; then
  echo "Toolchain ${TOOLCHAIN} is already available."
else
  echo "Install toolchain"
  elan toolchain install "${TOOLCHAIN}"
fi
