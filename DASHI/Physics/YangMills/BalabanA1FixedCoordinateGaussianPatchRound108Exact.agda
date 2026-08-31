{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1FixedCoordinateGaussianPatchRound108Exact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral

------------------------------------------------------------------------
-- Source-native fixed-coordinate Gaussian:
--
--   Ahat(U) = C(U)^* A(U) C(U)
--
-- after separating tangential free-coordinate motion (which must cancel against
-- the induced coordinate-volume Jacobian on the literal source carrier), only
--
--   middlePhysical = C^* A' C
--   normalConnection = genuine constrained-subspace motion
--
-- remains in the Gaussian beta projection.
------------------------------------------------------------------------

record FixedCoordinatePatchContribution : Set₁ where
  field
    middlePhysical normalConnection totalContribution : ℚ
    middleFloor normalBudget : ℚ

    totalExact : totalContribution ≡ middlePhysical + normalConnection
    middleLower : middleFloor ≤ middlePhysical
    normalConnectionLower : - normalBudget ≤ normalConnection

open FixedCoordinatePatchContribution public

fixedCoordinatePatchLower :
  (dataSet : FixedCoordinatePatchContribution) →
  middleFloor dataSet - normalBudget dataSet ≤ totalContribution dataSet
fixedCoordinatePatchLower dataSet =
  let
    summed :
      middleFloor dataSet + (- normalBudget dataSet)
      ≤ middlePhysical dataSet + normalConnection dataSet
    summed = ℚP.+-mono-≤
      (middleLower dataSet) (normalConnectionLower dataSet)
  in
  subst
    (λ upper → middleFloor dataSet - normalBudget dataSet ≤ upper)
    (sym (totalExact dataSet))
    (subst
      (λ lower → lower ≤ middlePhysical dataSet + normalConnection dataSet)
      (ℚRing.solve-∀ (middleFloor dataSet) (normalBudget dataSet))
      summed)

record FixedCoordinatePatchBox : Set₁ where
  field
    box : Integral.BoxIntegralEnclosure
    contribution : FixedCoordinatePatchContribution
    boxLowerIsRestrictedContribution :
      Integral.lowerContribution box ≡ totalContribution contribution

open FixedCoordinatePatchBox public

fixedCoordinateFloorBelowBoxLower :
  (patch : FixedCoordinatePatchBox) →
  middleFloor (contribution patch) - normalBudget (contribution patch)
  ≤ Integral.lowerContribution (box patch)
fixedCoordinateFloorBelowBoxLower patch =
  subst
    (λ upper →
      middleFloor (contribution patch) - normalBudget (contribution patch)
      ≤ upper)
    (sym (boxLowerIsRestrictedContribution patch))
    (fixedCoordinatePatchLower (contribution patch))

record FixedCoordinateGaussianPatchCertificate : Set₁ where
  field
    positivePatch : FixedCoordinatePatchBox
    complement : List Integral.BoxIntegralEnclosure

    -- The complement is the SAME restricted Gaussian trace and needs only sign.
    complementLowerNonnegative : 0ℚ ≤ Integral.boxLowerSum complement

    -- This is the genuinely useful positivity condition.
    fixedFloorPositive :
      0ℚ < middleFloor (contribution positivePatch)
        - normalBudget (contribution positivePatch)

open FixedCoordinateGaussianPatchCertificate public

fixedGaussianFloor : FixedCoordinateGaussianPatchCertificate → ℚ
fixedGaussianFloor dataSet =
  middleFloor (contribution (positivePatch dataSet))
    - normalBudget (contribution (positivePatch dataSet))

fixedGaussianFloorPositive :
  (dataSet : FixedCoordinateGaussianPatchCertificate) →
  0ℚ < fixedGaussianFloor dataSet
fixedGaussianFloorPositive = fixedFloorPositive

globalFixedCoordinateLowerFromPatch :
  (dataSet : FixedCoordinateGaussianPatchCertificate) →
  fixedGaussianFloor dataSet
  ≤ Integral.boxLowerSum
      (box (positivePatch dataSet) ∷ complement dataSet)
globalFixedCoordinateLowerFromPatch dataSet =
  let
    patchLower = fixedCoordinateFloorBelowBoxLower (positivePatch dataSet)
    rest = complementLowerNonnegative dataSet
    appendLower :
      Integral.lowerContribution (box (positivePatch dataSet))
      ≤ Integral.lowerContribution (box (positivePatch dataSet))
        + Integral.boxLowerSum (complement dataSet)
    appendLower =
      subst
        (λ left → left
          ≤ Integral.lowerContribution (box (positivePatch dataSet))
            + Integral.boxLowerSum (complement dataSet))
        (ℚP.+-identityʳ
          (Integral.lowerContribution (box (positivePatch dataSet))))
        (ℚP.+-monoʳ-≤
          (Integral.lowerContribution (box (positivePatch dataSet))) rest)
  in
  ℚP.≤-trans patchLower appendLower

round108FixedCoordinateGaussianPatchArithmeticLevel : ProofLevel
round108FixedCoordinateGaussianPatchArithmeticLevel = machineChecked

-- Physical/source leaves are now sharply separated:
--   1. middle C^*A'C positive patch, with A' using the literal mixed Wilson
--      third variation plus source gauge-fixing terms;
--   2. normal C' motion from the literal differentiated CMP98/99 constraint;
--   3. same-source tangential coordinate/Jacobian cancellation;
--   4. identification of the resulting restricted trace with betaZ.
literalCMP109MiddlePhysicalPatchRound108Level : ProofLevel
literalCMP109MiddlePhysicalPatchRound108Level = conditional

literalCMP99NormalSubspaceMotionBudgetRound108Level : ProofLevel
literalCMP99NormalSubspaceMotionBudgetRound108Level = conditional

literalCMP109TangentialCoordinateJacobianCancellationRound108Level : ProofLevel
literalCMP109TangentialCoordinateJacobianCancellationRound108Level = conditional

literalCMP109RestrictedGaussianTraceIsBetaZRound108Level : ProofLevel
literalCMP109RestrictedGaussianTraceIsBetaZRound108Level = conditional
