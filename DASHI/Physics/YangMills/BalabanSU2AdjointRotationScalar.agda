module DASHI.Physics.YangMills.BalabanSU2AdjointRotationScalar where

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_; oneR)

twoR : ℝ
twoR = oneR +R oneR

row00 row01 row02 row10 row11 row12 row20 row21 row22 :
  ℝ → ℝ → ℝ → ℝ → ℝ
row00 a b c d = (((a *R a) +R (b *R b)) +R (-R (c *R c))) +R (-R (d *R d))
row01 a b c d = twoR *R ((b *R c) +R (-R (a *R d)))
row02 a b c d = twoR *R ((b *R d) +R (a *R c))
row10 a b c d = twoR *R ((b *R c) +R (a *R d))
row11 a b c d = (((a *R a) +R (-R (b *R b))) +R (c *R c)) +R (-R (d *R d))
row12 a b c d = twoR *R ((c *R d) +R (-R (a *R b)))
row20 a b c d = twoR *R ((b *R d) +R (-R (a *R c)))
row21 a b c d = twoR *R ((c *R d) +R (a *R b))
row22 a b c d = (((a *R a) +R (-R (b *R b))) +R (-R (c *R c))) +R (d *R d)

rotationX rotationY rotationZ :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
rotationX a b c d x y z = ((row00 a b c d *R x) +R (row01 a b c d *R y)) +R (row02 a b c d *R z)
rotationY a b c d x y z = ((row10 a b c d *R x) +R (row11 a b c d *R y)) +R (row12 a b c d *R z)
rotationZ a b c d x y z = ((row20 a b c d *R x) +R (row21 a b c d *R y)) +R (row22 a b c d *R z)

inner0R inner1R inner2R inner3R :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
inner0R a b c d x y z = ((-R (b *R x)) +R (-R (c *R y))) +R (-R (d *R z))
inner1R a b c d x y z = ((a *R x) +R (c *R z)) +R (-R (d *R y))
inner2R a b c d x y z = ((a *R y) +R (-R (b *R z))) +R (d *R x)
inner3R a b c d x y z = ((a *R z) +R (b *R y)) +R (-R (c *R x))

adjointXExpandedR adjointYExpandedR adjointZExpandedR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
adjointXExpandedR a b c d x y z =
  (((inner0R a b c d x y z *R (-R b)) +R (inner1R a b c d x y z *R a)) +R (inner2R a b c d x y z *R (-R d))) +R (-R (inner3R a b c d x y z *R (-R c)))
adjointYExpandedR a b c d x y z =
  (((inner0R a b c d x y z *R (-R c)) +R (-R (inner1R a b c d x y z *R (-R d)))) +R (inner2R a b c d x y z *R a)) +R (inner3R a b c d x y z *R (-R b))
adjointZExpandedR a b c d x y z =
  (((inner0R a b c d x y z *R (-R d)) +R (inner1R a b c d x y z *R (-R c))) +R (-R (inner2R a b c d x y z *R (-R b)))) +R (inner3R a b c d x y z *R a)
