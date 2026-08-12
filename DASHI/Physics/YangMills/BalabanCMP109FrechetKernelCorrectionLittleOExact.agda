module DASHI.Physics.YangMills.BalabanCMP109FrechetKernelCorrectionLittleOExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Wojciech Dybalski, Alexander Stottmeister, Yoh Tanimoto,
-- "The Balaban variational problem in the non-linear sigma model",
-- arXiv:2403.09800 (2024). No DOI recorded in the supplied manuscript.
--
-- DASHI CONTRIBUTION
--
-- Record the strictly weaker tangent endpoint that is sufficient for Gate I.
-- A Lipschitz derivative gives an O(t^2) residual, but tangent equality only
-- needs the actual constraint map to be Frechet differentiable at A.  For a
-- kernel direction h,
--
--   C(A+t h) = o(t).
--
-- The already proved 4/3 normal reopening then gives c(t h)=o(t).  This module
-- proves the exact epsilon arithmetic:
--
--   residual <= eps * |t| * H,
--   correction <= (4/3) residual
--
-- implies
--
--   correction <= (4/3 eps) * |t| * H.
--
-- Therefore a same-object Frechet derivative identification can close the
-- tangent theorem even if a global two-point Lipschitz constant for beta is
-- inconvenient.  The stronger O(t^2) route remains useful but is not logically
-- necessary for tangent=kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter

littleOResidualBudget : ℚ → ℚ → ℚ → ℚ
littleOResidualBudget epsilon timeMagnitude directionScale =
  epsilon * timeMagnitude * directionScale

littleOCorrectionBudget : ℚ → ℚ → ℚ → ℚ
littleOCorrectionBudget epsilon timeMagnitude directionScale =
  (Quarter.fourThirds * epsilon) * timeMagnitude * directionScale

reopeningPreservesLittleOBudgetExact : ∀ epsilon timeMagnitude directionScale →
  Quarter.fourThirds
    * littleOResidualBudget epsilon timeMagnitude directionScale
  ≡ littleOCorrectionBudget epsilon timeMagnitude directionScale
reopeningPreservesLittleOBudgetExact epsilon timeMagnitude directionScale =
  ℚRing.solve-∀ epsilon timeMagnitude directionScale

frechetResidualToLittleOCorrection :
  ∀ residual correction epsilon timeMagnitude directionScale →
  0ℚ ≤ residual →
  residual ≤ littleOResidualBudget epsilon timeMagnitude directionScale →
  correction ≤ Quarter.fourThirds * residual →
  correction ≤ littleOCorrectionBudget epsilon timeMagnitude directionScale
frechetResidualToLittleOCorrection
    residual correction epsilon timeMagnitude directionScale
    residualNN residualUpper correctionUpper =
  let
    scaled = Norm.scaleNonnegative Quarter.fourThirds
      (ℚP.nonNegative⁻¹ Quarter.fourThirds) residualUpper
  in
  ℚP.≤-trans correctionUpper
    (subst
      (λ upper → Quarter.fourThirds * residual ≤ upper)
      (reopeningPreservesLittleOBudgetExact
        epsilon timeMagnitude directionScale)
      scaled)

-- A convenient exact formulation of the derivative quotient estimate after
-- dividing by a positive |t| is supplied by the consumer.  The epsilon factor
-- itself is enlarged only by 4/3.
littleOQuotientConstant : ℚ → ℚ
littleOQuotientConstant epsilon = Quarter.fourThirds * epsilon

littleOQuotientConstantExact : ∀ epsilon →
  littleOQuotientConstant epsilon ≡ (+ 4 / 3) * epsilon
littleOQuotientConstantExact epsilon = refl

cmp109FrechetResidualLittleOCorrectionLevel : ProofLevel
cmp109FrechetResidualLittleOCorrectionLevel = machineChecked

cmp109TangentNeedsOnlyFrechetRemainderLevel : ProofLevel
cmp109TangentNeedsOnlyFrechetRemainderLevel = machineChecked
