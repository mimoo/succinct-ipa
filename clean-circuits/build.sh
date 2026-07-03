#!/bin/sh
# Build the Genesis gadgets inside a clean checkout.
set -e
cd "$(dirname "$0")/.."
if [ ! -d clean-repo ]; then
  git clone --depth 1 https://github.com/Verified-zkEVM/clean.git clean-repo
fi
ln -sf ../../../clean-circuits/Genesis.lean clean-repo/Clean/Gadgets/Genesis.lean
ln -sf ../../../clean-circuits/GenesisCheck.lean clean-repo/Clean/Gadgets/GenesisCheck.lean
cd clean-repo
lake exe cache get
lake build Clean.Gadgets.Genesis Clean.Gadgets.GenesisCheck
