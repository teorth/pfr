/-!
# The fibring identity

The proof of the fibring identity, which is a key to the proof of PFR.
-/

/--  Let $\pi : H \to H'$ be a homomorphism between vector spaces over $\F_2$ and let $Z_1,Z_2$ be $H$-valued random variables. Then we have
  $$ d[Z_1; Z_2] \geq d[\pi(Z_1);\pi(Z_2)] + d[Z_1|\pi(Z_1); Z_2 |\pi(Z_2)].$$
  Moreover, if $Z_1,Z_2$ are taken to be independent, then the difference between the two sides is
$$I( Z_1 - Z_2 : (\pi(Z_1), \pi(Z_2))  |  \pi(Z_1 - Z_2) ).$$ -/
lemma fibring_ident : 0 = 1 := by sorry

/-- Let $Y_1,Y_2,Y_3$ and $Y_4$ be independent $G$-valued random variables.
  Then
$$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$
$$  + I[ Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4 ] = d[Y_1; Y_2] + d[ Y_3; Y_4].$$
-/
lemma fibring_ident' : 0 = 1 := by sorry
