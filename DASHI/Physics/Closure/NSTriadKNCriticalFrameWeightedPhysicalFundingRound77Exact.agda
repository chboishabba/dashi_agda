module DASHI.Physics.Closure.NSTriadKNCriticalFrameWeightedPhysicalFundingRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND77 / CRITICAL EVENT -> FRAME-WEIGHTED PHYSICAL CHARGE
--
-- Round73 required W<=1.  Round77 removes that absolute normalization.
-- A selected critical event instead carries its source-native frame product B
-- and an exact bound W<=B.  For a genuine positive critical excess mu>0,
-- positivity of B is DERIVED: if B=0 then the factorized concentration theorem
-- gives mu^2 <= Q B = 0, contradicting mu^2>0.  Rational positivity then
-- constructs the reciprocal rho canonically.
--
-- Hence, on the SAME atoms and SAME critical-ratio remainder,
--
--   mu^2 <= Q W <= Q B
--        and mu>0
--
-- imply
--
--   B>0,  rho=1/B,  rho mu^2 <= Q.
--
-- If Q is simultaneously identified with the event's physical charge, the
-- frame-weighted square rho mu^2 is a genuine Carleson floor.  No unit frame
-- bound, reciprocal premise, phase choice, square root, or free rescaling
-- remains.  The live C2/C3 frontier is therefore the same-object dynamic
-- overlay/charge identity, not normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational using
  (ℚ; 0ℚ; Positive; _*_; _+_; _≤_; _<_; _≢_; nonNegative; ≢-nonZero)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationFactorizedConcentrationRound72Exact as Factorized
import DASHI.Physics.Closure.NSTriadKNFrameWeightedSquareChargeRound77Exact as WeightedCharge
import DASHI.Physics.Closure.NSTriadKNFrameWeightedFinalAntichainBudgetRound77Exact as Final

record FrameBoundedCriticalOverlay
    {atoms : List Structured.LocalizedPDEAtom}
    (overlay : Overlay.TriadicFactorizationOverlay atoms)
    (frameProduct : ℚ) : Set where
  field
    frameNonnegative : 0ℚ ≤ frameProduct
    complexityBelowFrame :
      Overlay.overlayEffectiveComplexity overlay ≤ frameProduct

open FrameBoundedCriticalOverlay public

overlaySquareBelowChargeTimesFrame :
  ∀ {atoms frameProduct}
    (overlay : Overlay.TriadicFactorizationOverlay atoms) →
  FrameBoundedCriticalOverlay overlay frameProduct →
  L2.square (R71.triadicSignedSum atoms)
  ≤ Overlay.overlayCharge overlay * frameProduct
overlaySquareBelowChargeTimesFrame overlay bounded =
  let
    chargeNN = Effective.concentrationChargeNonnegative
      (Overlay.overlayFactors overlay)
    complexityNN = Effective.effectiveComplexityNonnegative
      (Overlay.overlayFactors overlay)
    scaled =
      L2.nonnegativeProductMonotone
        chargeNN complexityNN chargeNN (frameNonnegative bounded)
        ℚP.≤-refl (complexityBelowFrame bounded)
  in
  ℚP.≤-trans (Overlay.overlayCauchy overlay) scaled

criticalAmplificationForcesChargeTimesFrame :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms)
    (frameProduct : ℚ) →
  FrameBoundedCriticalOverlay overlay frameProduct →
  0ℚ ≤ mu →
  Amplification.inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  Amplification.remainder step n ≡ R71.triadicSignedSum atoms →
  L2.square mu ≤ Overlay.overlayCharge overlay * frameProduct
criticalAmplificationForcesChargeTimesFrame
    step n mu atoms overlay frameProduct bounded muNN excess remainderExact =
  let
    factorized :
      L2.square mu
      ≤ Overlay.overlayCharge overlay * Overlay.overlayEffectiveComplexity overlay
    factorized =
      Factorized.criticalAmplificationForcesFactorizedConcentration
        step n mu atoms overlay muNN excess remainderExact
    chargeNN = Effective.concentrationChargeNonnegative
      (Overlay.overlayFactors overlay)
    complexityNN = Effective.effectiveComplexityNonnegative
      (Overlay.overlayFactors overlay)
    scaled =
      L2.nonnegativeProductMonotone
        chargeNN complexityNN chargeNN (frameNonnegative bounded)
        ℚP.≤-refl (complexityBelowFrame bounded)
  in
  ℚP.≤-trans factorized scaled

positiveAmplificationForcesFrameNonzero :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms)
    (frameProduct : ℚ)
    (bounded : FrameBoundedCriticalOverlay overlay frameProduct) →
  Positive mu →
  Amplification.inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  Amplification.remainder step n ≡ R71.triadicSignedSum atoms →
  frameProduct ≢ 0ℚ
positiveAmplificationForcesFrameNonzero
    step n mu atoms overlay frameProduct bounded muPositive excess remainderExact
    frameZero =
  let
    instance
      muPositiveInstance : Positive mu
      muPositiveInstance = muPositive
      squarePositiveInstance : Positive (L2.square mu)
      squarePositiveInstance = ℚP.pos*pos⇒pos mu mu

    muNN : 0ℚ ≤ mu
    muNN = ℚP.<⇒≤ (ℚP.positive⁻¹ mu)

    productBound = criticalAmplificationForcesChargeTimesFrame
      step n mu atoms overlay frameProduct bounded muNN excess remainderExact

    squareBelowZero : L2.square mu ≤ 0ℚ
    squareBelowZero =
      subst
        (λ selectedFrame →
          L2.square mu ≤ Overlay.overlayCharge overlay * selectedFrame)
        frameZero
        productBound
      |> subst (L2.square mu ≤_) (ℚP.*-zeroʳ (Overlay.overlayCharge overlay))

    squarePositive : 0ℚ < L2.square mu
    squarePositive = ℚP.positive⁻¹ (L2.square mu)
  in
  ℚP.<-irrefl 0ℚ (ℚP.<-≤-trans squarePositive squareBelowZero)
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  x |> f = f x

positiveAmplificationForcesFramePositive :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms)
    (frameProduct : ℚ)
    (bounded : FrameBoundedCriticalOverlay overlay frameProduct) →
  Positive mu →
  Amplification.inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  Amplification.remainder step n ≡ R71.triadicSignedSum atoms →
  Positive frameProduct
positiveAmplificationForcesFramePositive
    step n mu atoms overlay frameProduct bounded muPositive excess remainderExact =
  let
    frameNonzero = positiveAmplificationForcesFrameNonzero
      step n mu atoms overlay frameProduct bounded
      muPositive excess remainderExact
    instance
      frameNN = nonNegative (frameNonnegative bounded)
      frameNZ = ≢-nonZero frameNonzero
  in
  ℚP.nonNeg∧nonZero⇒pos frameProduct

record PhysicalFrameWeightedAmplificationWitness
    {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms) : Set where
  field
    frameProduct : ℚ
    frameBounded : FrameBoundedCriticalOverlay overlay frameProduct

    amplificationPositive : Positive mu
    criticalExcess :
      Amplification.inherited step n + mu
      ≤ C1.normalizedCriticalRatio positiveBlock (suc n)
    remainderExact :
      Amplification.remainder step n ≡ R71.triadicSignedSum atoms

    physicalCharge : ℚ
    physicalChargeNonnegative : 0ℚ ≤ physicalCharge
    overlayChargeIsPhysicalCharge :
      Overlay.overlayCharge overlay ≡ physicalCharge

open PhysicalFrameWeightedAmplificationWitness public

amplificationNonnegative :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  PhysicalFrameWeightedAmplificationWitness step n mu atoms overlay →
  0ℚ ≤ mu
amplificationNonnegative witness =
  let
    instance
      muPositiveInstance : Positive _
      muPositiveInstance = amplificationPositive witness
  in
  ℚP.<⇒≤ (ℚP.positive⁻¹ _)

framePositive :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  (witness : PhysicalFrameWeightedAmplificationWitness step n mu atoms overlay) →
  Positive (frameProduct witness)
framePositive {step = step} {n = n} {mu = mu} {atoms = atoms} {overlay = overlay}
    witness =
  positiveAmplificationForcesFramePositive
    step n mu atoms overlay
    (frameProduct witness)
    (frameBounded witness)
    (amplificationPositive witness)
    (criticalExcess witness)
    (remainderExact witness)

reciprocalWeight :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  PhysicalFrameWeightedAmplificationWitness step n mu atoms overlay → ℚ
reciprocalWeight witness =
  WeightedCharge.safeRationalReciprocal (frameProduct witness)

reciprocalWitness :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  (witness : PhysicalFrameWeightedAmplificationWitness step n mu atoms overlay) →
  WeightedCharge.ReciprocalFrameWeight
    (frameProduct witness) (reciprocalWeight witness)
reciprocalWitness witness =
  WeightedCharge.positiveFrameReciprocal
    (frameProduct witness) (framePositive witness)

frameWeightedCriticalFloorBelowPhysicalCharge :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  (witness : PhysicalFrameWeightedAmplificationWitness
    step n mu atoms overlay) →
  reciprocalWeight witness * L2.square mu ≤ physicalCharge witness
frameWeightedCriticalFloorBelowPhysicalCharge
    {step = step} {n = n} {mu = mu} {atoms = atoms} {overlay = overlay}
    witness =
  let
    squareNN = L2.squareNonnegative mu
    chargeNN = Effective.concentrationChargeNonnegative
      (Overlay.overlayFactors overlay)
    productBound = criticalAmplificationForcesChargeTimesFrame
      step n mu atoms overlay
      (frameProduct witness)
      (frameBounded witness)
      (amplificationNonnegative witness)
      (criticalExcess witness)
      (remainderExact witness)
    weighted =
      WeightedCharge.reciprocalFrameWeightTurnsProductChargeIntoCharge
        squareNN chargeNN productBound (reciprocalWitness witness)
  in
  subst
    (λ upper → reciprocalWeight witness * L2.square mu ≤ upper)
    (overlayChargeIsPhysicalCharge witness)
    weighted

asFinalWeightedFundedNode :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  (witness : PhysicalFrameWeightedAmplificationWitness
    step n mu atoms overlay) →
  Final.FrameWeightedFundedNode
asFinalWeightedFundedNode {mu = mu} witness =
  Final.frame-weighted-funded-node
    (reciprocalWeight witness)
    mu
    (physicalCharge witness)
    (WeightedCharge.rhoNonnegative (reciprocalWitness witness))
    (frameWeightedCriticalFloorBelowPhysicalCharge witness)

round77CriticalEventNeedsAbsoluteUnitNormalization : Bool
round77CriticalEventNeedsAbsoluteUnitNormalization = false

round77PositiveCriticalEventForcesPositiveFrameProduct : Bool
round77PositiveCriticalEventForcesPositiveFrameProduct = true

round77CriticalFrameReciprocalIsConstructedNotAssumed : Bool
round77CriticalFrameReciprocalIsConstructedNotAssumed = true

round77FrameWeightedCriticalFundingCompilerConstructed : Bool
round77FrameWeightedCriticalFundingCompilerConstructed = true

round77SelectedTrajectoryProducesSameObjectFrameWeightedWitnesses : Bool
round77SelectedTrajectoryProducesSameObjectFrameWeightedWitnesses = false

round77DynamicCanonicalQPhysicalChargeIdentityConstructed : Bool
round77DynamicCanonicalQPhysicalChargeIdentityConstructed = false
