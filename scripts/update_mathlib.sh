# Update mathlib and the lean toolchain.
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake -Kenv=dev update # The `-Kenv=dev` is making sure we also update doc-gen
lake exe cache get
