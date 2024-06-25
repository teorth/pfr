import PFR.BoundingMutual


/-!
# Endgame for the Torsion PFR theorem


## Main definitions:


## Main results

-/

-- Now let $m \geq 2$, let $G$ be an $m$-torsion abelian group, and let $(X_i)_{1 \leq i \leq m}$ be a $\tau$-minimizer.

-- By a slight abuse of notation, we identify $\Z/m\Z$ and $\{1,\dots,m\}$ in the obvious way, and let $Y_{i,j}$ be an independent copy of $X_i$ for $i,j \in \Z/m\Z$.

-- W := \sum_{i,j \in \Z/m\Z} Y_{i,j}

-- Z_1 := \sum_{i,j \in \Z/m\Z} i Y_{i,j},
-- Z_2 := \sum_{i,j \in \Z/m\Z} j Y_{i,j},
-- Z_3 := \sum_{i,j \in \Z/m\Z} (-i-j) Y_{i,j}.

-- P_i := \sum_{j \in \Z/m\Z} Y_{i,j} ,
-- Q_j := \sum_{i \in \Z/m\Z} Y_{i,j} ,
-- R_r := \sum_{\substack{i,j \in \Z/m\Z \\ i+j=-r}} Y_{i,j}


/--  Z_1+Z_2+Z_3= 0 -/
lemma sum_of_z_eq_zero : 0 = 1 := sorry

/--   We have
  \[
    \bbI[Z_1 : Z_2\, |\, W],\
    \bbI[Z_2 : Z_3\, |\, W],\
    \bbI[Z_1 : Z_3\, |\, W] \leq t
  \]
  where $t :=  4m^2 \eta k$.
-/
lemma mutual_information_le_t : 0 = 1 := sorry


/-- We have $\bbH[W] \leq (2m-1)k + \frac1m \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_W_le : 0 = 1 := sorry

/-- We have $\bbH[Z_2] \leq (8m^2-16m+1) k + \frac{1}{m} \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_Z_two_le : 0 = 1 := sorry

/-- We have  $\bbI[W : Z_2] \leq 2 (m-1) k$. -/
lemma mutual_of_W_Z_two_le : 0 = 1 := sorry

/-- We have $\sum_{i=1}^m d[X_i;Z_2|W] \leq 8(m^3-m^2) k$. -/
lemma sum_of_conditional_distance_le : 0 = 1 := sorry


/-- Let $G$ be an abelian group, let $(T_1,T_2,T_3)$ be a $G^3$-valued random variable such that $T_1+T_2+T_3=0$ holds identically, and write
  \[
    \delta := \bbI[T_1 : T_2] + \bbI[T_1 : T_3] + \bbI[T_2 : T_3].
  \]
  Let $Y_1,\dots,Y_n$ be some further $G$-valued random variables and let $\alpha>0$ be a constant.
  Then there exists a random variable $U$ such that
$$    d[U;U] + \alpha \sum_{i=1}^n d[Y_i;U] \leq \Bigl(2 + \frac{\alpha n}{2} \Bigr) \delta + \alpha \sum_{i=1}^n d[Y_i;T_2].
$$
-/
lemma dist_of_U_add_le : 0 = 1 := sorry

/-- We have $k = 0$. -/
lemma k_eq_zero : 0 = 1 := sorry

/-- Suppose that $G$ is a finite abelian group of torsion $m$.  Suppose that $X$ is a $G$-valued random variable. Then there exists a subgroup $H \leq G$ such that \[ d[X;U_H] \leq 64 m^3 d[X;X].\] -/
lemma dist_of_X_U_H_le : 0 = 1 := sorry


/--Suppose that $G$ is a finite abelian group of torsion $m$.
  If $A \subset G$ is non-empty and $|A+A| \leq K|A|$, then $A$ can be covered by most $mK^{64m^3+1}$ translates of a subspace $H$ of $G$ with $|H| \leq |A|$.
-/
theorem torsion_PFR : 0 = 1 := sorry
