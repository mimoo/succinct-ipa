.PHONY: all lib circuits clean distclean

all: lib circuits

# Build the main SuccinctIPA library (mathlib-based).
lib:
	lake exe cache get
	lake build

# Build the formally verified Genesis gadgets inside a checkout of
# Verified-zkEVM/clean (clones clean-repo/ on first run).
circuits:
	./clean-circuits/build.sh

clean:
	rm -rf .lake

distclean: clean
	rm -rf clean-repo
