# Basic Lean Datastructures

This is a small collection of some definitions around basic data structures, e.g. Sets in Lean. It also contains additional theorems on datastructures from the standard library, e.g. Lists. The formalizations are in parts deviating from existing libraries like mathlib, as I do not need most of mathlib's machinery for my projects. For example, here we define a Set to be finite if (and only if) there exists a List with the same elements. 

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:

- Install `elan`, e.g. via `nix-shell -p elan` or simply `nix develop` if you are using nix.
- Run `lake build` to build the project. If the build is successful, the proofs are correct :tada:

