---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

{% include mathjax.html %}

# The Polynomial Freiman-Ruzsa Conjecture

The purpose of this repository is to hold a Lean4 formalization of [the proof of the Polynomial Freiman-Ruzsa (PFR) conjecture](https://arxiv.org/abs/2311.05762) (see also [this blog post](https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton)).  The statement is as follows: if $$A$$ is a non-empty subset of $${\bf F}_2^n$$ such that $$\vert A+A\vert \leq K\vert A\vert$$, then $$A$$ can be covered by at most $$2K^{12}$$ cosets of a subspace $$H$$ of $${\bf F}_2^n$$ of cardinality at most $$\vert A\vert$$.  The proof relies on the theory of Shannon entropy, so in particular development of the Shannon entropy inequalities will be needed.

* [Discussion of the project on Zulip](https://leanprover.zulipchat.com/#narrow/stream/412902-Polynomial-Freiman-Ruzsa-conjecture)
* [Blueprint of the proof](https://teorth.github.io/pfr/blueprint)
* [Documentation of the methods](https://teorth.github.io/pfr/docs)
* [A quick "tour" of the project](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour)
* [Some example Lean code to illustrate the results in the project](https://github.com/teorth/pfr/blob/master/examples.lean)
* [An (automatically generated) list of contributors to the project](https://github.com/teorth/pfr/graphs/contributors)

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/teorth/pfr)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip install -r blueprint/requirements.txt
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

## Moving material to mathlib

The project is now over. As such, we are currently working towards stabilising the new results and contributing them to mathlib.

Here is the list of files that do not depend on any other PFR file, indicating they are good candidates for upstreaming to mathlib:

{% include files_to_upstream.md %}

## Source reference

`[GGMT]`: <https://arxiv.org/abs/2311.05762>

[GGMT]: https://arxiv.org/abs/2311.05762
