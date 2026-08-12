module DASHI.Physics.YangMills.BalabanCMP109Equation012IdentityDerivativeCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Compute the exact first-order cancellation built into printed equation
-- (0.12).  At the identity reference, left-trivialized multiplication,
-- inversion, principal log and the outer exponential all have identity first
-- derivative.  For one Lie coordinate the relative product therefore has
--
--   ds_x + dcross_x + dt_x - dU_c.
--
-- Equation (0.12) averages this over the block, exponentiates, and multiplies
-- by U_c.  If the block weight is normalized, the averaged -dU_c term cancels
-- the final +dU_c exactly.  Hence
--
--   DQ_I = w sum_x (ds_x + dcross_x + dt_x).
--
-- This is the algebraic reason the reference derivative is a genuine block
-- path average rather than an independent direct-coarse contribution.  The
-- theorem is finite, exact, and componentwise; the remaining physical work is
-- to instantiate ds/dcross/dt by the already exact holonomy and Federbush
-- contour derivative formulas.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)

relativeReferenceDerivative :
  ∀ {Fine : Set} →
  (Fine → ℚ) → (Fine → ℚ) → (Fine → ℚ) → ℚ → Fine → ℚ
relativeReferenceDerivative source crossing target coarse fine =
  source fine + (crossing fine + (target fine - coarse))

threePathDerivative :
  ∀ {Fine : Set} →
  (Fine → ℚ) → (Fine → ℚ) → (Fine → ℚ) → Fine → ℚ
threePathDerivative source crossing target fine =
  source fine + (crossing fine + target fine)

referenceLieAverageDerivative :
  ∀ {Fine : Set} →
  ℚ → List Fine →
  (Fine → ℚ) → (Fine → ℚ) → (Fine → ℚ) → ℚ → ℚ
referenceLieAverageDerivative weight fines source crossing target coarse =
  weight * sumRational fines
    (relativeReferenceDerivative source crossing target coarse)

referenceEquation012Derivative :
  ∀ {Fine : Set} →
  ℚ → List Fine →
  (Fine → ℚ) → (Fine → ℚ) → (Fine → ℚ) → ℚ → ℚ
referenceEquation012Derivative weight fines source crossing target coarse =
  referenceLieAverageDerivative weight fines source crossing target coarse
  + coarse

sumThreePathExact :
  ∀ {Fine : Set} (fines : List Fine) source crossing target →
  sumRational fines (threePathDerivative source crossing target)
  ≡ sumRational fines source
    + (sumRational fines crossing + sumRational fines target)
sumThreePathExact fines source crossing target =
  trans
    (sumRationalAdd fines source
      (λ fine → crossing fine + target fine))
    (cong (sumRational fines source +_)
      (sumRationalAdd fines crossing target))

sumRelativeSplitsCoarse :
  ∀ {Fine : Set} (fines : List Fine) source crossing target coarse →
  sumRational fines
    (relativeReferenceDerivative source crossing target coarse)
  ≡ sumRational fines (threePathDerivative source crossing target)
    - natAsRational (Data.List.Base.length fines) * coarse
sumRelativeSplitsCoarse [] source crossing target coarse = ℚRing.solve []
sumRelativeSplitsCoarse (fine ∷ fines) source crossing target coarse
  rewrite sumRelativeSplitsCoarse fines source crossing target coarse =
  ℚRing.solve-∀
    (source fine) (crossing fine) (target fine) coarse
    (sumRational fines (threePathDerivative source crossing target))
    (natAsRational (Data.List.Base.length fines))

normalizedCoarseCancellation :
  ∀ weight count coarse →
  weight * count ≡ 1ℚ →
  ∀ pathSum →
  weight * (pathSum - count * coarse) + coarse
  ≡ weight * pathSum
normalizedCoarseCancellation weight count coarse normalized pathSum
  rewrite normalized = ℚRing.solve-∀ weight pathSum coarse

equation012IdentityDerivativeCancellation :
  ∀ {Fine : Set}
    weight (fines : List Fine) source crossing target coarse →
  weight * natAsRational (Data.List.Base.length fines) ≡ 1ℚ →
  referenceEquation012Derivative
    weight fines source crossing target coarse
  ≡ weight * sumRational fines
      (threePathDerivative source crossing target)
equation012IdentityDerivativeCancellation
    weight fines source crossing target coarse normalized =
  trans
    (cong (λ total → weight * total + coarse)
      (sumRelativeSplitsCoarse fines source crossing target coarse))
    (normalizedCoarseCancellation
      weight (natAsRational (Data.List.Base.length fines)) coarse
      normalized
      (sumRational fines (threePathDerivative source crossing target)))

cmp109Equation012IdentityCoarseCancellationLevel : ProofLevel
cmp109Equation012IdentityCoarseCancellationLevel = machineChecked
