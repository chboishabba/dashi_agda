module DASHI.Cognition.PNF.GrokkingEquivarianceDefectGeometryExact where

------------------------------------------------------------------------
-- SOURCES
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted.
--
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted.
--
-- DASHI CONTRIBUTION
-- An exact task-dynamical geometry comparison on the existing nine-point C3
-- modular regression.  The defect counts failures to intertwine translation of
-- the first task operand with translation of the output phase.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact as Grok
import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

Phase : Set
Phase = Wheel.DepthWheelPhase

advancePhase : Phase → Phase
advancePhase x = Character.phaseComposeC3 Wheel.phase-1 x

shiftLeft : Grok.InputPair → Grok.InputPair
shiftLeft Grok.p00 = Grok.p10
shiftLeft Grok.p01 = Grok.p11
shiftLeft Grok.p02 = Grok.p12
shiftLeft Grok.p10 = Grok.p20
shiftLeft Grok.p11 = Grok.p21
shiftLeft Grok.p12 = Grok.p22
shiftLeft Grok.p20 = Grok.p00
shiftLeft Grok.p21 = Grok.p01
shiftLeft Grok.p22 = Grok.p02

eqPhase : Phase → Phase → Bool
eqPhase Wheel.phase-0 Wheel.phase-0 = true
eqPhase Wheel.phase-0 Wheel.phase-1 = false
eqPhase Wheel.phase-0 Wheel.phase-2 = false
eqPhase Wheel.phase-1 Wheel.phase-0 = false
eqPhase Wheel.phase-1 Wheel.phase-1 = true
eqPhase Wheel.phase-1 Wheel.phase-2 = false
eqPhase Wheel.phase-2 Wheel.phase-0 = false
eqPhase Wheel.phase-2 Wheel.phase-1 = false
eqPhase Wheel.phase-2 Wheel.phase-2 = true

defectBit : Bool → Nat
defectBit true = 0
defectBit false = 1

equivarianceDefectAt :
  (Grok.InputPair → Phase) → Grok.InputPair → Nat
equivarianceDefectAt rule pair =
  defectBit
    (eqPhase
      (rule (shiftLeft pair))
      (advancePhase (rule pair)))

equivarianceDefect : (Grok.InputPair → Phase) → Nat
equivarianceDefect rule =
  equivarianceDefectAt rule Grok.p00
  + equivarianceDefectAt rule Grok.p01
  + equivarianceDefectAt rule Grok.p02
  + equivarianceDefectAt rule Grok.p10
  + equivarianceDefectAt rule Grok.p11
  + equivarianceDefectAt rule Grok.p12
  + equivarianceDefectAt rule Grok.p20
  + equivarianceDefectAt rule Grok.p21
  + equivarianceDefectAt rule Grok.p22

algorithmicEquivarianceDefectIsZero :
  equivarianceDefect Grok.algorithmicRule ≡ 0
algorithmicEquivarianceDefectIsZero = refl

memorizerEquivarianceDefectIsTwo :
  equivarianceDefect Grok.memorizerRule ≡ 2
memorizerEquivarianceDefectIsTwo = refl

characterGeometryStrictlyImprovesTaskActionDefect :
  equivarianceDefect Grok.algorithmicRule
  < equivarianceDefect Grok.memorizerRule
characterGeometryStrictlyImprovesTaskActionDefect = s≤s z≤n

------------------------------------------------------------------------
-- Localize the two failures: they are precisely the two directed action edges
-- incident to the malformed held-out p22 value in this cyclic first-coordinate
-- action.
------------------------------------------------------------------------

memorizerDefectEnteringHeldOut :
  equivarianceDefectAt Grok.memorizerRule Grok.p12 ≡ 1
memorizerDefectEnteringHeldOut = refl

memorizerDefectLeavingHeldOut :
  equivarianceDefectAt Grok.memorizerRule Grok.p22 ≡ 1
memorizerDefectLeavingHeldOut = refl

algorithmicHeldOutEdgesRemainEquivariant :
  equivarianceDefectAt Grok.algorithmicRule Grok.p12 ≡ 0
  × equivarianceDefectAt Grok.algorithmicRule Grok.p22 ≡ 0
algorithmicHeldOutEdgesRemainEquivariant = refl , refl

------------------------------------------------------------------------
-- This is a finite task-action distortion, not a claim that all grokking runs
-- monotonically optimize this particular count.  It does establish the exact
-- comparison requested by the representation-geometry programme: the
-- structural character rule realizes the task action with strictly smaller
-- dynamical/equivariance defect than the training-fitting memorizer.
------------------------------------------------------------------------
