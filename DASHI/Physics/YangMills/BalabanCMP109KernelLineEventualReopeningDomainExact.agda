module DASHI.Physics.YangMills.BalabanCMP109KernelLineEventualReopeningDomainExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- DASHI CONTRIBUTION
--
-- Close the small seam between a kernel-line Frechet little-o estimate and
-- the already-proved quarter-contraction reopening theorem.  The nonlinear
-- normal solver is only valid on a stated residual ball.  It is therefore not
-- enough to know informally that C(A+t h)=o(t): the residual must eventually
-- be shown to belong to that exact ball.
--
-- The theorem below is deliberately division-free.  A concrete Frechet
-- producer supplies
--
--   residualNorm <= epsilon * |t| * directionScale,
--
-- and the chosen small-time gate supplies
--
--   epsilon * |t| * directionScale <= reopeningRadius.
--
-- Transitivity gives eventual domain membership.  No continuity or
-- differentiability of the fixed-point correction t |-> c_t is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

LittleOBudget : ℚ → ℚ → ℚ → ℚ
LittleOBudget epsilon timeMagnitude directionScale =
  epsilon * timeMagnitude * directionScale

record ReopeningBall : Set₁ where
  field
    radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius

open ReopeningBall public

InReopeningDomain : ReopeningBall → ℚ → Set
InReopeningDomain ball residualNorm = residualNorm ≤ radius ball

littleOBudgetEntersReopeningDomain :
  ∀ (ball : ReopeningBall)
    residualNorm epsilon timeMagnitude directionScale →
  residualNorm ≤ LittleOBudget epsilon timeMagnitude directionScale →
  LittleOBudget epsilon timeMagnitude directionScale ≤ radius ball →
  InReopeningDomain ball residualNorm
littleOBudgetEntersReopeningDomain ball residualNorm epsilon timeMagnitude directionScale
    residualUpper smallTime =
  ℚP.≤-trans residualUpper smallTime

------------------------------------------------------------------------
-- Exact quarter-reopening compatibility.
--
-- Once the residual is in-domain and the SAME fixed-point correction obeys
-- the literal quarter remainder estimate, its norm is controlled by 4/3 of
-- the residual.  Combining the two inequalities gives the exact epsilon
-- enlargement used by tangent geometry.
------------------------------------------------------------------------

littleOBudgetCorrectionUpper :
  ∀ correctionNorm residualNorm epsilon timeMagnitude directionScale →
  correctionNorm ≤ Quarter.fourThirds * residualNorm →
  residualNorm ≤ LittleOBudget epsilon timeMagnitude directionScale →
  correctionNorm
    ≤ Quarter.fourThirds * LittleOBudget epsilon timeMagnitude directionScale
littleOBudgetCorrectionUpper correctionNorm residualNorm epsilon timeMagnitude directionScale
    correctionUpper residualUpper =
  ℚP.≤-trans correctionUpper
    (Norm.scaleNonnegative Quarter.fourThirds
      (ℚP.nonNegative⁻¹ Quarter.fourThirds)
      residualUpper)

------------------------------------------------------------------------
-- A small-time witness can be represented directly as a producer.  This is
-- the exact formal shape needed by a later real/Bishop little-o limit theorem:
-- it need only return a positive-enough time gate whose budget lies below the
-- solver radius; no global IFT is reintroduced.
------------------------------------------------------------------------

record EventualReopeningDomainWitness (ball : ReopeningBall) : Set₁ where
  field
    epsilon : ℚ
    directionScale : ℚ
    timeGate : ℚ
    budgetAtGateBelowRadius :
      LittleOBudget epsilon timeGate directionScale ≤ radius ball

open EventualReopeningDomainWitness public

cmp109KernelLineEventualReopeningDomainLevel : ProofLevel
cmp109KernelLineEventualReopeningDomainLevel = machineChecked

cmp109KernelLineCorrectionNeedsNoCurveContinuityLevel : ProofLevel
cmp109KernelLineCorrectionNeedsNoCurveContinuityLevel = machineChecked
