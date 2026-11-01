module DASHI.Physics.YangMills.BalabanYM4ROperationShellTransferExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Exact RG1b source dictionary at the scalar shell level.  If a literal
-- Bałaban R-activity on rooted shell n factors as
--
--   activity <= p0 * diameterWeight,
--
-- with p0 <= 1/4 and diameterWeight <= 2^{-n}, then it is already below the
-- repository's KP shell majorant (1/4)2^{-n}.  No second large-field decay
-- convention is needed between the primary R-operation estimate and Step V.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as P2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ROperationShellDatum (depth : Nat) : Set where
  field
    activity p0 diameterWeight : ℚ

    diameterNonnegative : 0ℚ ≤ diameterWeight

    activityFactorized : activity ≤ p0 * diameterWeight
    p0BelowQuarter : p0 ≤ P2.quarter
    diameterBelowHalfPower : diameterWeight ≤ P2.halfPower depth

open ROperationShellDatum public

rOperationShellBelowKPMajorant :
  ∀ depth (datum : ROperationShellDatum depth) →
  activity datum ≤ P2.shellMajorant depth
rOperationShellBelowKPMajorant depth datum =
  let
    scaledP0 :
      diameterWeight datum * p0 datum
      ≤ diameterWeight datum * P2.quarter
    scaledP0 = Norm.scaleNonnegative
      (diameterWeight datum)
      (diameterNonnegative datum)
      (p0BelowQuarter datum)

    reorderedP0 :
      p0 datum * diameterWeight datum
      ≤ P2.quarter * diameterWeight datum
    reorderedP0 =
      subst
        (λ left → left ≤ P2.quarter * diameterWeight datum)
        (ℚRing.solve-∀ (p0 datum) (diameterWeight datum))
        (subst
          (λ right → diameterWeight datum * p0 datum ≤ right)
          (ℚRing.solve-∀ P2.quarter (diameterWeight datum))
          scaledP0)

    scaledDiameter :
      P2.quarter * diameterWeight datum
      ≤ P2.quarter * P2.halfPower depth
    scaledDiameter = Norm.scaleNonnegative
      P2.quarter
      (ℚP.nonNegative⁻¹ P2.quarter)
      (diameterBelowHalfPower datum)
  in
  ℚP.≤-trans
    (activityFactorized datum)
    (ℚP.≤-trans reorderedP0 scaledDiameter)

ym4ROperationToKPShellArithmeticLevel : ProofLevel
ym4ROperationToKPShellArithmeticLevel = machineChecked

-- Remaining source-specific RG1b producer: identify Bałaban's literal
-- boundary-uniform R^(k)(X) norm, p0 suppression and diameter factor with the
-- fields above on every physical rooted shell.
ym4PhysicalROperationShellInstantiationLevel : ProofLevel
ym4PhysicalROperationShellInstantiationLevel = conditional
