import PFR.Homomorphism
import Mathlib.Combinatorics.Additive.Energy

/-!
# The approximate homomorphism form of PFR

Here we apply PFR to show that almost homomorphisms f from a 2-group to a 2-group often coincide with a (shifted) actual homomorphisms.  Here, approximate is in the sense that f(x+y)=f(x)+f(y) is true for a positive proportion of x,y.

## Main result

* `approx_hom_pfr` : If $f: G → G'$ is a map between finite abelian elementary 2-groups such that $f(x+y)=f(x)+f(y)$ for at least $|G|/K$ values, then then there is a homomorphism $\phi: G \to G'$ and a constant $c$ such that $f(x)=\phi(x)+c$ for a substantial set of values.

-/
open Pointwise Classical

variable {G : Type*} [AddCommGroup G] (A : Finset G)

/-- If $G$ is a group, and $A$ is a finite subset of $G$, the \emph{additive energy} $E(A)$ of $A$ is the number of quadruples $(a_1,a_2,a_3,a_4) \in A^4$ such that $a_1+a_2 = a_3+a_4$. -/
notation3:max "E[" A "]" => Finset.additiveEnergy A A

/--  If $G$ is a group, $A,B$ are finite subsets of $G$, then
$$ E(A) \geq \frac{|\{ (a,a') \in A \times A: a+a' \in B \}|^2}{|B|}.$$ -/
lemma cauchy_schwarz (A B : Finset G) :
  ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd ∈ B)).card^2 ≤ B.card * E[A] := sorry

-- in order to state bsg we may need to temporarily define some placeholder constants C_1, C_2, C_3, C_4

/-- Let $G$ be an abelian group, and let $A$ be a finite non-empty set with $E(A) \geq |A|^3 / K$ for some $K \geq 1$.  Then there is a subset $A'$ of $A$ with $|A'| \geq |A| / (C_1 K^{C_2})$ and $|A'+A'| \leq C_3 K^{C_4} |A'|$ -/
proof_wanted bsg : 0 = 1


/-- Let $G,G'$ be finite abelian $2$-groups.
  Let $f: G \to G'$ be a function, and suppose that there are at least $|G|^2 / K$ pairs $(x,y) \in G^2$ such that
$$ f(x+y) = f(x) + f(y).$$
Then there exists a homomorphism $\phi: G \to G'$ and a constant $c \in G'$ such that $f(x) = \phi(x)+c$ for at least $|G| / 4C_1 C_3^{24} K^{2C_4+48 C_2}$ values of $x \in G$. -/
proof_wanted approx_hom_pfr : 0 = 1
