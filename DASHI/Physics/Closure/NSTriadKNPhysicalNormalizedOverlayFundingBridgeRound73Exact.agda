module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedOverlayFundingBridgeRound73Exact where

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
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Historical conference article; no DOI assigned.
--
-- ROUND73 / SAME-OBJECT NORMALIZED OVERLAY -> PHYSICAL EVENT
--
-- Normalising W is useful only if Q is simultaneously tied to a genuine
-- physical charge.  Otherwise reciprocal rescaling can make W smaller by
-- making Q larger without changing the signed atom values.
--
-- This file therefore packages the exact joint obligation.  On one SAME
-- critical-ratio step and one SAME Round62 LocalizedPDEAtom list it requires:
--
--   * critical excess mu;
--   * exact remainder = triadicSignedSum(atoms);
--   * a factorization overlay on those atoms;
--   * effective complexity W <= 1;
--   * one explicit physical charge equal to overlayCharge.
--
-- The resulting theorem constructs the exact Round73 funding event
--
--      mu^2 <= physicalCharge.
--
-- Thus arbitrary factor rescaling cannot improve the proof for free: any
-- rescaling that increases Q increases the actual charge that must fit under
-- the one finite physical budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNNormalizedEffectiveComplexityConcentrationRound73Exact as Normalized
import DASHI.Physics.Closure.NSTriadKNSquareChargeFundingCompilerRound73Exact as SquareFunding

record PhysicalNormalizedAmplificationWitness
    {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms) : Set where
  field
    normalizedComplexity : Normalized.NormalizedEffectiveComplexity overlay
    amplificationNonnegative : 0ℚ ≤ mu
    criticalExcess :
      Amplification.inherited step n + mu
      ≤ C1.normalizedCriticalRatio positiveBlock (suc n)
    remainderExact :
      Amplification.remainder step n ≡ R71.triadicSignedSum atoms

    physicalCharge : ℚ
    physicalChargeNonnegative : 0ℚ ≤ physicalCharge
    overlayChargeIsPhysicalCharge :
      Overlay.overlayCharge overlay ≡ physicalCharge

open PhysicalNormalizedAmplificationWitness public

normalizedWitnessSquareBelowPhysicalCharge :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  PhysicalNormalizedAmplificationWitness step n mu atoms overlay →
  L2.square mu ≤ physicalCharge
normalizedWitnessSquareBelowPhysicalCharge
    {step = step} {n = n} {mu = mu} {atoms = atoms} {overlay = overlay}
    witness =
  subst
    (λ upper → L2.square mu ≤ upper)
    (overlayChargeIsPhysicalCharge witness)
    (Normalized.criticalAmplificationForcesNormalizedCharge
      step n mu atoms overlay
      (normalizedComplexity witness)
      (amplificationNonnegative witness)
      (criticalExcess witness)
      (remainderExact witness))

normalizedWitnessAsSquareChargedEvent :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  PhysicalNormalizedAmplificationWitness step n mu atoms overlay →
  SquareFunding.SquareChargedAmplificationEvent
normalizedWitnessAsSquareChargedEvent {mu = mu} witness =
  SquareFunding.square-charged-amplification-event
    mu
    (physicalCharge witness)
    (physicalChargeNonnegative witness)
    (normalizedWitnessSquareBelowPhysicalCharge witness)

round73NormalizedOverlayWeldedToPhysicalChargeEvent : Bool
round73NormalizedOverlayWeldedToPhysicalChargeEvent = true

round73OverlayChargeIdentityIsRequiredForPhysicalFunding : Bool
round73OverlayChargeIdentityIsRequiredForPhysicalFunding = true

round73SelectedTrajectoryProducesPhysicalNormalizedWitnesses : Bool
round73SelectedTrajectoryProducesPhysicalNormalizedWitnesses = false

round73NormalizedOverlayWeldedToPhysicalChargeEventIsTrue :
  round73NormalizedOverlayWeldedToPhysicalChargeEvent ≡ true
round73NormalizedOverlayWeldedToPhysicalChargeEventIsTrue = refl

round73SelectedTrajectoryProducesPhysicalNormalizedWitnessesIsFalse :
  round73SelectedTrajectoryProducesPhysicalNormalizedWitnesses ≡ false
round73SelectedTrajectoryProducesPhysicalNormalizedWitnessesIsFalse = refl
