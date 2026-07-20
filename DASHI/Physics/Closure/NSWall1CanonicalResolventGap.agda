module DASHI.Physics.Closure.NSWall1CanonicalResolventGap where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_; +<+)
open import Data.Nat.Properties as ℕ using (≤-refl)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; *≤*; *<*; _/_)

open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier
open import DASHI.Physics.Closure.NSWall1RationalScalarInstance

------------------------------------------------------------------------
-- Exact six-mode packet baseline.
--
-- This is deliberately not identified with the physical NS low block.  It
-- proves the arithmetic and exposes the representation theorem required for
-- promotion to the actual Wall-1 operator.
------------------------------------------------------------------------

eight sixtyFour sixtyFive : ℚ
eight = (+ 8) / 1
sixtyFour = (+ 64) / 1
sixtyFive = (+ 65) / 1

data CanonicalLowVector : Set where
  lowVector : ℚ → ℚ → ℚ → CanonicalLowVector

lowEnergy : CanonicalLowVector → ℚ
lowEnergy (lowVector a b c) =
  rationalL1Majorant (vec3 a b c)

canonicalK00 : CanonicalLowVector → CanonicalLowVector
canonicalK00 _ = lowVector 0ℚ 0ℚ 0ℚ

canonicalLowResolvent : CanonicalLowVector → CanonicalLowVector
canonicalLowResolvent x = x

canonicalResolventEquation :
  ∀ x → canonicalLowResolvent x ≡ x
canonicalResolventEquation x = refl

rational≤refl : ∀ q → q ≤ q
rational≤refl q = *≤* (+<+-to-≤)
  where
  +<+-to-≤ = Data.Integer.Base.+≤+ ℕ.≤-refl

canonicalLowResolventBound :
  ∀ x → lowEnergy (canonicalLowResolvent x) ≤ 1ℚ * lowEnergy x
canonicalLowResolventBound x = rational≤refl (lowEnergy x)

canonicalC01 canonicalR0 canonicalC10 : ℚ
canonicalC01 = eight
canonicalR0 = 1ℚ
canonicalC10 = eight

canonicalCorrectionBudget : ℚ
canonicalCorrectionBudget = canonicalC10 * (canonicalR0 * canonicalC01)

canonicalBudgetNormalizes : canonicalCorrectionBudget ≡ sixtyFour
canonicalBudgetNormalizes = refl

canonicalStrictPacketGap : canonicalCorrectionBudget < sixtyFive
canonicalStrictPacketGap = *<* (+<+ ℕ.≤-refl)

record CanonicalPacketNSRepresentation
    {v : Level}
    (ShellVector : Set v) : Set (lsuc v) where
  field
    actualLowResolventEnergy : ShellVector → ℚ
    actualCorrectionBudget : ℚ
    actualHighGap : ℚ

    lowResolventMatchesBaseline :
      ∀ x → actualLowResolventEnergy x ≤ canonicalR0

    correctionBudgetMatches :
      actualCorrectionBudget ≡ canonicalCorrectionBudget

    highGapDominatesPacketGap :
      sixtyFive ≤ actualHighGap

open CanonicalPacketNSRepresentation public
