# Building a Mathlib-Dependent Lean 4 Project on NixOS

This document outlines how to set up, manage, and build a Lean 4 project dependent on **Mathlib** on NixOS using a Nix development shell.

---

## 1. Nix Environment Setup

Mathlib downloads precompiled binary artifacts (`.olean` caches) via `curl` and `git`. On NixOS, Lake needs access to `elan` (the Lean version manager) and system root certificates (`cacert`) to prevent SSL download failures.

See the flake.nix file in this directory

# 1. Enter the Nix development shell
nix develop

# 2. Fetch Mathlib's matching Lean toolchain (Only do this if you want to overwrite your lean-toolchain with Mathlib's latest release)
curl -s -o lean-toolchain [https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain)

# 3. Resolve and pin dependency commits in lake-manifest.json (bumps all dependencies to latest upstream)
lake update <pkg>

# 4. Fetch precompiled .olean build caches from GitHub Releases
lake exe cache get

# 5. Fast build (only compiles your project modules)
lake build




