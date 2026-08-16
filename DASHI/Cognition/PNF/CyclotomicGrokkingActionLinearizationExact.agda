module DASHI.Cognition.PNF.CyclotomicGrokkingActionLinearizationExact where

------------------------------------------------------------------------
-- SOURCES
--
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted.
--
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted.
--
-- SOURCE BOUNDARY
-- The papers motivate learned Fourier/phase structure for modular arithmetic.
-- DASHI proves the exact finite C3 algebra below; it does not assert that every
-- network learns this representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact as Grok
import DASHI.Cognition.PNF.TaskActionRepresentationGeometryExact as Geometry
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as Cyclo
import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Every modular-addition pair is carried into multiplication in Q(omega).
------------------------------------------------------------------------

algorithmicPairLinearises : (pair : Grok.InputPair) →
  Cyclo.root (Grok.algorithmicRule pair)
  ≡ Cyclo.root (Grok.leftPhase pair)
      Cyclo.*C Cyclo.root (Grok.rightPhase pair)
algorithmicPairLinearises pair =
  Cyclo.rootCharacterHomomorphism
    (Grok.leftPhase pair) (Grok.rightPhase pair)

phaseOneActsByOmegaOnEveryState : (x : Wheel.DepthWheelPhase) →
  Cyclo.root (Character.phaseComposeC3 Wheel.phase-1 x)
  ≡ Cyclo.omega Cyclo.*C Cyclo.root x
phaseOneActsByOmegaOnEveryState x =
  Geometry.actionCommutesWithEncoding
    Geometry.c3CyclotomicRepresentation Wheel.phase-1 x

------------------------------------------------------------------------
-- Training fit and structural extension remain distinct.  The memorizer still
-- agrees on all eight declared training pairs, while the cyclotomic structural
-- rule fixes the held-out p22 answer through the same multiplication law.
------------------------------------------------------------------------

memorizerStillFitsTraining :
  Grok.TrainingEquivalent Grok.memorizerRule Grok.algorithmicRule
memorizerStillFitsTraining = Grok.memorizerAndAlgorithmTrainingEquivalent

heldOutAlgorithmicPhase : Grok.algorithmicRule Grok.p22 ≡ Wheel.phase-1
heldOutAlgorithmicPhase = Grok.heldOutCorrectAnswer

heldOutCyclotomicFactorization :
  Cyclo.root (Grok.algorithmicRule Grok.p22)
  ≡ Cyclo.root Wheel.phase-2 Cyclo.*C Cyclo.root Wheel.phase-2
heldOutCyclotomicFactorization = algorithmicPairLinearises Grok.p22

memorizerDoesNotDetermineFullTask :
  Grok.FullTaskEquivalent Grok.memorizerRule Grok.algorithmicRule → ⊥
memorizerDoesNotDetermineFullTask = Grok.memorizerAndAlgorithmNotFullTaskEquivalent

record GrokkingGeometryBoundary : Set where
  field
    exactTaskActionLinearises : Bool
    exactTaskActionLinearisesIsTrue : exactTaskActionLinearises ≡ true
    trainingFitAloneDeterminesCyclotomicRule : Bool
    trainingFitAloneDeterminesCyclotomicRuleIsFalse :
      trainingFitAloneDeterminesCyclotomicRule ≡ false

canonicalGrokkingGeometryBoundary : GrokkingGeometryBoundary
canonicalGrokkingGeometryBoundary = record
  { exactTaskActionLinearises = true
  ; exactTaskActionLinearisesIsTrue = refl
  ; trainingFitAloneDeterminesCyclotomicRule = false
  ; trainingFitAloneDeterminesCyclotomicRuleIsFalse = refl
  }

------------------------------------------------------------------------
-- The substantive geometric simplification is the commuting action law:
-- modular addition in the task carrier becomes multiplication by roots of unity
-- in the latent carrier.  This is stronger than a spectral-amplitude receipt.
------------------------------------------------------------------------
