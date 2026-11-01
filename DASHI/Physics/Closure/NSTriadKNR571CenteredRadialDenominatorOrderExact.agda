module DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 DIVISION-FREE RADIAL-DENOMINATOR ORDER COMPILER
--
-- Let
--
--   D = rP + rQ - 2 rK
--   S = rP + rQ + 2 rK.
--
-- Once the centered geometry supplies
--
--   D * S <= B,
--
-- with nonnegative radii and nonnegative B, no division by S is needed.
-- Since S >= rK:
--
--   * if D <= 0, then rK*D <= 0 <= B;
--   * if 0 <= D, then rK*D <= S*D = D*S <= B.
--
-- Hence
--
--   rK * (rP+rQ-2rK) <= B.
--
-- For the live centered A2 carrier the intended B is 4|y|^2.  This owner is
-- deliberately pure ordered-rational plumbing: it introduces no annular lower
-- bound, inverse radius, square root, shell count, or PDE estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

two : ℚ
two = 1ℚ + 1ℚ

centeredExcess : ℚ → ℚ → ℚ → ℚ
centeredExcess rP rQ rK = rP + rQ - two * rK

centeredSum : ℚ → ℚ → ℚ → ℚ
centeredSum rP rQ rK = rP + rQ + two * rK

record CenteredRadialProductBudget : Set where
  constructor centered-radial-product-budget
  field
    radiusP radiusQ radiusK budget : ℚ
    radiusPNonnegative : 0ℚ ≤ radiusP
    radiusQNonnegative : 0ℚ ≤ radiusQ
    radiusKNonnegative : 0ℚ ≤ radiusK
    budgetNonnegative : 0ℚ ≤ budget
    clearedProductBound :
      centeredExcess radiusP radiusQ radiusK
        * centeredSum radiusP radiusQ radiusK
      ≤ budget

open CenteredRadialProductBudget public

radiusKBelowCenteredSum :
  (D : CenteredRadialProductBudget) →
  radiusK D ≤ centeredSum (radiusP D) (radiusQ D) (radiusK D)
radiusKBelowCenteredSum D =
  let
    rP = radiusP D
    rQ = radiusQ D
    rK = radiusK D

    rest : ℚ
    rest = rP + rQ + rK

    restNN : 0ℚ ≤ rest
    restNN = Rational.addNonnegative
      (Rational.addNonnegative (radiusPNonnegative D) (radiusQNonnegative D))
      (radiusKNonnegative D)

    raw : rK + 0ℚ ≤ rK + rest
    raw = ℚP.+-mono-≤ ℚP.≤-refl restNN
  in
  subst
    (rK ≤_)
    (solve (rP ∷ rQ ∷ rK ∷ []))
    (subst
      (_≤ rK + rest)
      (ℚP.+-identityʳ rK)
      raw)

centeredRadialCurvatureFromClearedProduct :
  (D : CenteredRadialProductBudget) →
  radiusK D * centeredExcess (radiusP D) (radiusQ D) (radiusK D)
  ≤ budget D
centeredRadialCurvatureFromClearedProduct D
  with ℚP.≤-total
    (centeredExcess (radiusP D) (radiusQ D) (radiusK D)) 0ℚ
... | inj₁ excessNonpositive =
  let
    rK = radiusK D
    excess = centeredExcess (radiusP D) (radiusQ D) rK

    instance
      rKNN = ℚ.nonNegative (radiusKNonnegative D)

    raw : rK * excess ≤ rK * 0ℚ
    raw = ℚP.*-monoˡ-≤-nonNeg rK excessNonpositive

    belowZero : rK * excess ≤ 0ℚ
    belowZero =
      subst
        (rK * excess ≤_)
        (solve (rK ∷ []))
        raw
  in
  ℚP.≤-trans belowZero (budgetNonnegative D)
... | inj₂ excessNonnegative =
  let
    rP = radiusP D
    rQ = radiusQ D
    rK = radiusK D
    excess = centeredExcess rP rQ rK
    total = centeredSum rP rQ rK

    instance
      excessNN = ℚ.nonNegative excessNonnegative

    raised : rK * excess ≤ total * excess
    raised =
      ℚP.*-monoʳ-≤-nonNeg excess (radiusKBelowCenteredSum D)

    commute : total * excess ≡ excess * total
    commute = solve (total ∷ excess ∷ [])
  in
  ℚP.≤-trans
    raised
    (subst
      (_≤ budget D)
      (sym commute)
      (clearedProductBound D))

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

r571A2DivisionFreeDenominatorCompilerClosed : Bool
r571A2DivisionFreeDenominatorCompilerClosed = true

r571A2RequiresAnnularPositiveLowerBound : Bool
r571A2RequiresAnnularPositiveLowerBound = false

r571A2RequiresRadiusDivision : Bool
r571A2RequiresRadiusDivision = false

r571A2LiteralCenteredProductBridgeClosedHere : Bool
r571A2LiteralCenteredProductBridgeClosedHere = false

r571A2UniformCurvatureClosedHere : Bool
r571A2UniformCurvatureClosedHere = false

r571A2DivisionFreeDenominatorCompilerClosedIsTrue :
  r571A2DivisionFreeDenominatorCompilerClosed ≡ true
r571A2DivisionFreeDenominatorCompilerClosedIsTrue = refl

r571A2RequiresAnnularPositiveLowerBoundIsFalse :
  r571A2RequiresAnnularPositiveLowerBound ≡ false
r571A2RequiresAnnularPositiveLowerBoundIsFalse = refl

r571A2RequiresRadiusDivisionIsFalse :
  r571A2RequiresRadiusDivision ≡ false
r571A2RequiresRadiusDivisionIsFalse = refl

r571A2LiteralCenteredProductBridgeClosedHereIsFalse :
  r571A2LiteralCenteredProductBridgeClosedHere ≡ false
r571A2LiteralCenteredProductBridgeClosedHereIsFalse = refl
