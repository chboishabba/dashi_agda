module DASHI.Physics.Gravity.KSW668F8OriginalTTSourcePrimitiveJetExact where

------------------------------------------------------------------------
-- XXXV: EXACT original KSW668 F8 fourth-order TT source vs its
-- original conservative FV endpoint-primitive owner.
-- Reuse only; do not replace scripts/ksw668_f8_fv_source_flux.py or
-- scripts/ksw668_f8_tt_multipole.py.
--
-- Variables (f0,f1,f2,f3,f4) are formal radial derivative jet
-- coordinates for original smooth compact scalar f(u); the input
-- u=r/eps. These finite ring theorems expand the PRODUCT RULE for
-- derivative of each ORIGINAL endpoint primitive.
--
-- l=0: d P0 /du = u² G0, effective d=3 source weighted density.
-- l=2: d P2 /du = u^6 G2, effective d=7 weighted density.
-- l=4: d P4 /du +27 u² f = u^10 G4, effective d=11.
--
-- A separate analytic calculus theorem must identify those formal
-- jet-polynomial derivatives with actual f'(u), etc and establish
-- compact boundary flatness, not merely their finite arithmetic.
-- Pinned Agda kernel NOT RUN. No ESD edits; original attribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

u2 u3 u4 u5 u6 : ℚ → ℚ
u2 u = u * u
u3 u = u2 u * u
u4 u = u2 u * u2 u
u5 u = u4 u * u
u6 u = u4 u * u2 u

-- Weighted original regularized modes u^(2+2ell) G_ell(u):
-- formulas are exactly those in scripts/ksw668_f8_tt_multipole.py.
originalWeightedSource0 :
  ℚ → ℚ → ℚ → ℚ → ℚ
originalWeightedSource0 u f2 f3 f4 =
  ((+ 2) / 5) * (u2 u * f4 + ((+ 4) / 1) * u * f3)

originalWeightedSource2 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
originalWeightedSource2 u f1 f2 f3 f4 =
  ((+ 4) / 7) * (u4 u * f4 + u3 u * f3
    + - (((+ 6) / 1) * u2 u * f2)
    + ((+ 6) / 1) * u * f1)

originalWeightedSource4 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
originalWeightedSource4 u f1 f2 f3 f4 =
  ((+ 1) / 35) * (u6 u * f4
    + - (((+ 6) / 1) * u5 u * f3)
    + ((+ 15) / 1) * u4 u * f2
    + - (((+ 15) / 1) * u3 u * f1))

-- Explicit formal PRODUCT RULE applied to original endpoint
-- primitives P0=(2/5)(u² f3+2u f2-2 f1),
-- P2=(4/7)(u^4 f3-3u³ f2+3u² f1),
-- P4=(u^6 f3-12u^5 f2+75u^4 f1-315u³ f0)/35.
productDerivativeP0 :
  ℚ → ℚ → ℚ → ℚ → ℚ
productDerivativeP0 u f2 f3 f4 =
  ((+ 2) / 5) *
    (((+ 2) / 1) * u * f3 + u2 u * f4
    + ((+ 2) / 1) * f2 + ((+ 2) / 1) * u * f3
    + - (((+ 2) / 1) * f2))

productDerivativeP2 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
productDerivativeP2 u f1 f2 f3 f4 =
  ((+ 4) / 7) *
    (((+ 4) / 1) * u3 u * f3 + u4 u * f4
    + - (((+ 9) / 1) * u2 u * f2)
    + - (((+ 3) / 1) * u3 u * f3)
    + ((+ 6) / 1) * u * f1
    + ((+ 3) / 1) * u2 u * f2)

productDerivativeP4 :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
productDerivativeP4 u f0 f1 f2 f3 f4 =
  ((+ 1) / 35) *
    (((+ 6) / 1) * u5 u * f3 + u6 u * f4
    + - (((+ 60) / 1) * u4 u * f2)
    + - (((+ 12) / 1) * u5 u * f3)
    + ((+ 300) / 1) * u3 u * f1
    + ((+ 75) / 1) * u4 u * f2
    + - (((+ 945) / 1) * u2 u * f0)
    + - (((+ 315) / 1) * u3 u * f1))

originalTTSourcePrimitive0Exact :
  (u f2 f3 f4 : ℚ) →
  productDerivativeP0 u f2 f3 f4
    ≡ originalWeightedSource0 u f2 f3 f4
originalTTSourcePrimitive0Exact u f2 f3 f4 = solve []

originalTTSourcePrimitive2Exact :
  (u f1 f2 f3 f4 : ℚ) →
  productDerivativeP2 u f1 f2 f3 f4
    ≡ originalWeightedSource2 u f1 f2 f3 f4
originalTTSourcePrimitive2Exact u f1 f2 f3 f4 = solve []

originalTTSourcePrimitive4WithRemainderExact :
  (u f0 f1 f2 f3 f4 : ℚ) →
  productDerivativeP4 u f0 f1 f2 f3 f4
    + ((+ 27) / 1) * u2 u * f0
    ≡ originalWeightedSource4 u f1 f2 f3 f4
originalTTSourcePrimitive4WithRemainderExact u f0 f1 f2 f3 f4 = solve []
