The purpose of this repository is to hold a Lean4 formalization of <A HREF="https://arxiv.org/abs/2311.05762">the proof of the Polynomial Freiman-Ruzsa (PFR) conjecture</A> (see also <A HREF="https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton/">this blog post</A>.  The statement is as follows: if $A$ is a non-empty subset of ${\bf F}_2^n$ such that $|A+A| \leq K|A|$, then $A$ can be covered by at most $2K^{12}$ cosets of a subspace $H$ of ${\bf F}_2^n$ of cardinality at most $|A|$.  The proof relies on the theory of Shannon entropy, so in particular development of the Shannon entropy inequalities will be needed.

* <A HREF="https://leanprover.zulipchat.com/#narrow/stream/412902-Polynomial-Freiman-Ruzsa-conjecture">Discussion of the project on Zulip</A>
* <A HREF="https://teorth.github.io/pfr/blueprint">Blueprint of the proof</A>
* <A HREF="https://teorth.github.io/pfr/docs">Documentation of the methods</A>
* <A HREF="https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/">A quick "tour" of the project</A>

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To build the project, run `lake exe cache get` and then `lake build`.

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip3 install invoke pandoc
cd .. # go to folder where you are happy clone git repos
git clone git@github.com:plastex/plastex
pip3 install ./plastex
git clone git@github.com:PatrickMassot/leanblueprint
pip3 install ./leanblueprint
cd sphere-eversion
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.

## Source reference

`[GGMT]`: <https://arxiv.org/abs/2311.05762>

[GGMT]: https://arxiv.org/abs/2311.05762
