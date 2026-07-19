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
rotationX a b c d x y z =
  ((row00 a b c d *R x) +R (row01 a b c d *R y)) +R (row02 a b c d *R z)
rotationY a b c d x y z =
  ((row10 a b c d *R x) +R (row11 a b c d *R y)) +R (row12 a b c d *R z)
rotationZ a b c d x y z =
  ((row20 a b c d *R x) +R (row21 a b c d *R y)) +R (row22 a b c d *R z)
