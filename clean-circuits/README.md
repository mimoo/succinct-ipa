# clean-circuits — formally verified Genesis layer gadgets

Canonical sources for the [clean](https://github.com/Verified-zkEVM/clean)
(Verified-zkEVM) gadgets that verify the Genesis circuit layers
(see `../solutions/2-genesis.md`, `../sage/`).

- `Genesis.lean` — the gadgets: Poseidon rounds, exponent-chain steps,
  Tonelli–Shanks conditional step, QR bit, curve evaluation, complete
  Renes–Costello–Batina point addition. Each is a `FormalCircuit` with
  soundness AND completeness proven; specs are plain functions mirrored
  verbatim by the Sage layers, pinned by `#eval` test vectors over the
  Pallas base field.
- `GenesisCheck.lean` — `#print axioms` check (no `sorry`).

## Build

```sh
./build.sh    # clones clean (pinned), symlinks the sources in, builds
```
