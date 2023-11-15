---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

{% include mathjax.html %}

# The Polynomial Freiman-Ruzsa Conjecture

The purpose of this repository is to hold a Lean4 formalization of the proof of the Polynomial Freiman-Ruzsa (PFR) conjecture, recently proven in <https://arxiv.org/abs/2311.05762>.  The statement is as follows: if $$A$$ is a non-empty subset of $${\bf F}_2^n$$ such that $$\vert A+A\vert \leq K\vert A\vert$$, then $$A$$ can be covered by at most $$2K^{12}$$ cosets of a subspace $$H$$ of $${\bf F}_2^n$$ of cardinality at most $$\vert A\vert$$.  The proof relies on the theory of Shannon entropy, so in particular development of the Shannon entropy inequalities will be needed.

Discussion of the project will be held on this Zulip stream: <https://leanprover.zulipchat.com/#narrow/stream/412902-Polynomial-Freiman-Ruzsa-conjecture>

Additional discussion of the project may be found at <https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton/>

## Source reference

`[GGMT]`: <https://arxiv.org/abs/2311.05762>

[GGMT]: https://arxiv.org/abs/2311.05762
