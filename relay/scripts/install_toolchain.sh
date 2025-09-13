GAMES=$1
OWNER=$2
REPO=$3

cd ${GAMES}

echo "Read toolchain."
TOOLCHAIN=$(head ${OWNER}/${REPO}/lean-toolchain)

echo "Install toolchain"
elan toolchain install ${TOOLCHAIN}
