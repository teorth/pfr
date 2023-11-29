import PFR.main

open Pointwise

variable {G G' : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [AddCommGroup G'] [ElementaryAddCommGroup G' 2] [Fintype G']

/-- Let $H_0$ be a subgroup of $G$.  Then every homomorphism $\phi: H_0 \to G'$ can be extended to a homomorphism $\tilde \phi: G \to G'$. -/
lemma hahn_banach : 0 = 1 := sorry


/-- Let $H$ be a subgroup of $G \times G'$.  Then there exists a subgroup $H_0$ of $G$, a subgroup $H_1$ of $G'$, and a homomorphism $\phi: G \to G'$ such that
$$ H := \{ (x, \phi(x) + y): x \in H_0, y \in H_1 \}.$$
In particular, $|H| = |H_0| |H_1|$. -/
lemma goursat : 0 = 1 := by sorry


/-- Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{ f(x) - \phi(x)\}| \leq 4 |S|^{24}.$$ -/
lemma homomorphism_pfr : 0 = 1 := by sorry
