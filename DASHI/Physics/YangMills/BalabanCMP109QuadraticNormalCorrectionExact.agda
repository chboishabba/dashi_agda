module DASHI.Physics.YangMills.BalabanCMP109QuadraticNormalCorrectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Separate the tangent theorem's genuinely local analytic input from the
-- already-proved uniform derivative budget.  Uniform smallness makes the
-- Newton map contractive, but tangent identification requires a first-order
-- modulus so that a kernel direction has only quadratic constraint residual.
--
-- The finite scalar core is:
--
--   residual(t h) <= (L/2) t^2 |h|^2,
--   correction      <= (4/3) residual,
--
-- hence
--
--   correction <= (2L/3) t^2 |h|^2.
--
-- This is the exact O(t^2) estimate needed to construct a constraint-preserving
-- curve with derivative h.  No limiting theorem is hidden here: the consumer
-- must separately supply the complete-real curve/fixed-point realization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter

oneHalf twoThirds : ℚ
oneHalf = + 1 / 2
twoThirds = + 2 / 3

quadraticResidualBudget : ℚ → ℚ → ℚ → ℚ
quadraticResidualBudget lipschitz time directionNormSq =
  oneHalf * lipschitz * (time * time) * directionNormSq

quadraticCorrectionBudget : ℚ → ℚ → ℚ → ℚ
quadraticCorrectionBudget lipschitz time directionNormSq =
  twoThirds * lipschitz * (time * time) * directionNormSq

fourThirdsTimesHalfExact : ∀ lipschitz time directionNormSq →
  Quarter.fourThirds
    * quadraticResidualBudget lipschitz time directionNormSq
  ≡ quadraticCorrectionBudget lipschitz time directionNormSq
fourThirdsTimesHalfExact lipschitz time directionNormSq =
  ℚRing.solve-∀ lipschitz time directionNormSq

quadraticNormalCorrection :
  ∀ residualNorm correctionNorm lipschitz time directionNormSq →
  0ℚ ≤ residualNorm →
  residualNorm ≤ quadraticResidualBudget lipschitz time directionNormSq →
  correctionNorm ≤ Quarter.fourThirds * residualNorm →
  correctionNorm ≤ quadraticCorrectionBudget lipschitz time directionNormSq
quadraticNormalCorrection residualNorm correctionNorm
    lipschitz time directionNormSq residualNonnegative residualUpper correctionUpper =
  let
    scaledResidual :
      Quarter.fourThirds * residualNorm
      ≤ Quarter.fourThirds
          * quadraticResidualBudget lipschitz time directionNormSq
    scaledResidual =
      Norm.scaleNonnegative Quarter.fourThirds
        (ℚP.nonNegative⁻¹ Quarter.fourThirds) residualUpper
  in
  ℚP.≤-trans correctionUpper
    (subst
      (λ upper → Quarter.fourThirds * residualNorm ≤ upper)
      (fourThirdsTimesHalfExact lipschitz time directionNormSq)
      scaledResidual)

record KernelDirectionQuadraticResidual : Set₁ where
  field
    residualNorm correctionNorm lipschitz time directionNormSq : ℚ
    residualNonnegative : 0ℚ ≤ residualNorm
    residualQuadratic :
      residualNorm ≤ quadraticResidualBudget lipschitz time directionNormSq
    quarterReopening :
      correctionNorm ≤ Quarter.fourThirds * residualNorm

open KernelDirectionQuadraticResidual public

kernelDirectionCorrectionQuadratic :
  ∀ dataSet →
  correctionNorm dataSet
  ≤ quadraticCorrectionBudget
      (lipschitz dataSet) (time dataSet) (directionNormSq dataSet)
kernelDirectionCorrectionQuadratic dataSet =
  quadraticNormalCorrection
    (residualNorm dataSet)
    (correctionNorm dataSet)
    (lipschitz dataSet)
    (time dataSet)
    (directionNormSq dataSet)
    (residualNonnegative dataSet)
    (residualQuadratic dataSet)
    (quarterReopening dataSet)

cmp109QuadraticResidualToCorrectionLevel : ProofLevel
cmp109QuadraticResidualToCorrectionLevel = machineChecked

cmp109KernelDirectionQuadraticCorrectionLevel : ProofLevel
cmp109KernelDirectionQuadraticCorrectionLevel = machineChecked

physicalCMP109LocalDerivativeModulusInputLevel : ProofLevel
physicalCMP109LocalDerivativeModulusInputLevel = conditional
