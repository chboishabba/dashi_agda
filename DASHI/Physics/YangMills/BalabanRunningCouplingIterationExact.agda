module DASHI.Physics.YangMills.BalabanRunningCouplingIterationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_)
import Data.Nat.Properties as ℕP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact using
  (pow2)
open import DASHI.Physics.YangMills.BalabanDyadicTerminalScaleExact using
  (ScaleRatio; scaleRatio; RatioEqual; spacingAfterSteps)

------------------------------------------------------------------------
-- Exact iteration of the inverse-coupling recursion.
--
-- The analytic one-step theorem has the form
--
--   u_{k+1} = u_k - betaStep + rho_k,
--
-- where u_k = g_k^{-2}.  This module proves by induction that the physical
-- sequence equals the ideal affine flow plus the accumulated remainder.  The
-- beta coefficient and the remainder estimate are not assumed again at every
-- scale.
------------------------------------------------------------------------

idealInverseCoupling : ℚ → ℚ → Nat → ℚ
idealInverseCoupling initial betaStep zero = initial
idealInverseCoupling initial betaStep (suc step) =
  idealInverseCoupling initial betaStep step - betaStep

accumulatedBetaRemainder : (Nat → ℚ) → Nat → ℚ
accumulatedBetaRemainder remainder zero = 0ℚ
accumulatedBetaRemainder remainder (suc step) =
  accumulatedBetaRemainder remainder step + remainder step

recursiveInverseCoupling : ℚ → ℚ → (Nat → ℚ) → Nat → ℚ
recursiveInverseCoupling initial betaStep remainder zero = initial
recursiveInverseCoupling initial betaStep remainder (suc step) =
  recursiveInverseCoupling initial betaStep remainder step
    - betaStep + remainder step

recursionReassociation : ∀ ideal accumulated betaStep remainder →
  (ideal + accumulated) - betaStep + remainder
  ≡ (ideal - betaStep) + (accumulated + remainder)
recursionReassociation = ℚRing.solve-∀

addZeroRight : ∀ value → value ≡ value + 0ℚ
addZeroRight = ℚRing.solve-∀

iteratedInverseCouplingFormula :
  ∀ initial betaStep remainder step →
  recursiveInverseCoupling initial betaStep remainder step
  ≡ idealInverseCoupling initial betaStep step
    + accumulatedBetaRemainder remainder step
iteratedInverseCouplingFormula initial betaStep remainder zero =
  addZeroRight initial
iteratedInverseCouplingFormula initial betaStep remainder (suc step)
  rewrite iteratedInverseCouplingFormula initial betaStep remainder step =
  recursionReassociation
    (idealInverseCoupling initial betaStep step)
    (accumulatedBetaRemainder remainder step)
    betaStep
    (remainder step)

record PhysicalRunningCouplingRecursion : Set₁ where
  field
    physicalInverseCouplingSq : Nat → ℚ
    initialInverseCouplingSq betaStep : ℚ
    betaRemainder : Nat → ℚ

    physicalInitial :
      physicalInverseCouplingSq zero ≡ initialInverseCouplingSq

    physicalOneStep : ∀ step →
      physicalInverseCouplingSq (suc step)
      ≡ physicalInverseCouplingSq step - betaStep + betaRemainder step

open PhysicalRunningCouplingRecursion public

physicalMatchesRecursiveInverseCoupling :
  (flow : PhysicalRunningCouplingRecursion) → ∀ step →
  physicalInverseCouplingSq flow step
  ≡ recursiveInverseCoupling
      (initialInverseCouplingSq flow)
      (betaStep flow)
      (betaRemainder flow)
      step
physicalMatchesRecursiveInverseCoupling flow zero = physicalInitial flow
physicalMatchesRecursiveInverseCoupling flow (suc step)
  rewrite physicalOneStep flow step
  | physicalMatchesRecursiveInverseCoupling flow step = refl

physicalIteratedInverseCouplingFormula :
  (flow : PhysicalRunningCouplingRecursion) → ∀ step →
  physicalInverseCouplingSq flow step
  ≡ idealInverseCoupling
      (initialInverseCouplingSq flow)
      (betaStep flow)
      step
    + accumulatedBetaRemainder (betaRemainder flow) step
physicalIteratedInverseCouplingFormula flow step =
  trans
    (physicalMatchesRecursiveInverseCoupling flow step)
    (iteratedInverseCouplingFormula
      (initialInverseCouplingSq flow)
      (betaStep flow)
      (betaRemainder flow)
      step)

------------------------------------------------------------------------
-- Exact relation between a bounded terminal-step offset and physical dyadic
-- spacing.  If k*(N) = N+d, then 2^{k*(N)}/2^N = 2^d.  Consequently the hard
-- dimensional-transmutation estimate can target a bounded integer offset.
------------------------------------------------------------------------

pow2Add : ∀ left right →
  pow2 (left + right) ≡ pow2 left * pow2 right
pow2Add zero right = sym (ℕP.*-identityˡ (pow2 right))
pow2Add (suc left) right
  rewrite pow2Add left right =
  sym (ℕP.*-assoc (suc (suc zero)) (pow2 left) (pow2 right))

terminalOffsetSpacingExact : ∀ exponent offset →
  RatioEqual
    (spacingAfterSteps exponent (exponent + offset))
    (scaleRatio (pow2 offset) (suc zero))
terminalOffsetSpacingExact exponent offset =
  trans
    (ℕP.*-identityʳ (pow2 (exponent + offset)))
    (trans
      (pow2Add exponent offset)
      (ℕP.*-comm (pow2 exponent) (pow2 offset)))

record BoundedTerminalStepOffset : Set₁ where
  field
    physicalTerminalStep : Nat → Nat
    terminalOffset : Nat → Nat
    maximumOffset : Nat

    terminalStepIsExponentPlusOffset : ∀ exponent →
      physicalTerminalStep exponent ≡ exponent + terminalOffset exponent

    terminalOffsetPowerBelowMaximum : ∀ exponent →
      pow2 (terminalOffset exponent) ℕP.≤ pow2 maximumOffset

open BoundedTerminalStepOffset public

physicalTerminalSpacingHasOffsetScale :
  (window : BoundedTerminalStepOffset) → ∀ exponent →
  RatioEqual
    (spacingAfterSteps exponent (physicalTerminalStep window exponent))
    (scaleRatio (pow2 (terminalOffset window exponent)) (suc zero))
physicalTerminalSpacingHasOffsetScale window exponent
  rewrite terminalStepIsExponentPlusOffset window exponent =
  terminalOffsetSpacingExact exponent (terminalOffset window exponent)

------------------------------------------------------------------------
-- One-step RG invariance implies invariance along every finite RG trajectory.
------------------------------------------------------------------------

record TransmutationOneStepInvariant (Scale Coupling : Set) : Set₁ where
  field
    blockScale : Scale → Scale
    runningStep : Coupling → Coupling
    transmutationScale : Scale → Coupling → Scale
    EqualScale : Scale → Scale → Set
    equalScaleRefl : ∀ scale → EqualScale scale scale
    equalScaleTrans : ∀ {left middle right} →
      EqualScale left middle → EqualScale middle right → EqualScale left right

    oneStepInvariant : ∀ scale coupling →
      EqualScale
        (transmutationScale scale coupling)
        (transmutationScale (blockScale scale) (runningStep coupling))

open TransmutationOneStepInvariant public

iterate : ∀ {A : Set} → (A → A) → Nat → A → A
iterate step zero value = value
iterate step (suc count) value = iterate step count (step value)

transmutationScaleFiniteRGInvariant :
  ∀ {Scale Coupling}
    (dataSet : TransmutationOneStepInvariant Scale Coupling) →
  ∀ count scale coupling →
  EqualScale dataSet
    (transmutationScale dataSet scale coupling)
    (transmutationScale dataSet
      (iterate (blockScale dataSet) count scale)
      (iterate (runningStep dataSet) count coupling))
transmutationScaleFiniteRGInvariant dataSet zero scale coupling =
  equalScaleRefl dataSet (transmutationScale dataSet scale coupling)
transmutationScaleFiniteRGInvariant dataSet (suc count) scale coupling =
  equalScaleTrans dataSet
    (oneStepInvariant dataSet scale coupling)
    (transmutationScaleFiniteRGInvariant dataSet count
      (blockScale dataSet scale)
      (runningStep dataSet coupling))

runningCouplingFiniteIterationLevel : ProofLevel
runningCouplingFiniteIterationLevel = machineChecked

terminalOffsetSpacingFactorizationLevel : ProofLevel
terminalOffsetSpacingFactorizationLevel = machineChecked

finiteRGTransmutationInvarianceAssemblyLevel : ProofLevel
finiteRGTransmutationInvarianceAssemblyLevel = machineChecked

physicalBetaRemainderEstimateLevel : ProofLevel
physicalBetaRemainderEstimateLevel = conditional

physicalTerminalOffsetBoundLevel : ProofLevel
physicalTerminalOffsetBoundLevel = conjectural
