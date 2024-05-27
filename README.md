# The Polynomial Freiman-Ruzsa Conjecture

[![GitHub CI](https://github.com/teorth/pfr/actions/workflows/push.yml/badge.svg)](https://github.com/teorth/pfr/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/teorth/pfr)

The original purpose of this repository is to hold a Lean4 formalization of [the proof of the Polynomial Freiman-Ruzsa (PFR) conjecture](https://arxiv.org/abs/2311.05762) of Katalin Marton (see also [this blog post](https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton)).  The statement is as follows: if $A$ is a non-empty subset of ${\bf F}_2^n$ such that $|A+A| \leq K|A|$, then $A$ can be covered by at most $2K^{12}$ cosets of a subspace $H$ of ${\bf F}_2^n$ of cardinality at most $|A|$.  The proof relies on the theory of Shannon entropy, so in particular development of the Shannon entropy inequalities was needed.

After the primary purpose of the project was completed, a second stage of the project developed several consequences of PFR, as well as an argument of Jyun-Jie Liao that reduced the exponent $12$ to $11$.  This second stage has also been completed.

Currently, the project is obtaining an extension of PFR to other bounded torsion groups, as well as formalizing a further refinement of Jyun-Jie Liao that improves the exponent further to $9$.

* [Discussion of the project on Zulip](https://leanprover.zulipchat.com/#narrow/stream/412902-Polynomial-Freiman-Ruzsa-conjecture)
* [Blueprint of the proof](https://teorth.github.io/pfr/blueprint)
* [Documentation of the methods](https://teorth.github.io/pfr/docs)
* [A quick "tour" of the project](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour)
* [Some example Lean code to illustrate the results in the project](https://github.com/teorth/pfr/blob/master/examples.lean)

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To build the project, run `lake exe cache get` and then `lake build`.

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:

```
sudo apt install graphviz libgraphviz-dev
pip uninstall -y leanblueprint
pip install -r blueprint/requirements.txt
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.

Or you can just run `inv dev` instead of `inv all` and `inv serve`, after each edit to the LaTeX,
it will automatically rebuild the blueprint, you just need to refresh the web page to see the rendered result.

Note: If you have something wrong in your LaTeX file, and the LaTeX compilation fails,
LaTeX will stuck and ask for commands, you'll need to type `X` then return to exit LaTeX,
then fix the LaTeX error, and run `inv dev` again.

## Moving material to mathlib

As the first two phases of the project are completed, we are currently working towards stabilising the new results and contributing them to mathlib.

## Source reference

`[GGMT]`: <https://arxiv.org/abs/2311.05762>

`[L]` : <https://arxiv.org/abs/2404.09639>

`[GGMT2]`: <https://arxiv.org/abs/2404.02244>
