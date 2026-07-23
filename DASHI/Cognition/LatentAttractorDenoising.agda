module DASHI.Cognition.LatentAttractorDenoising where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.CognitiveResearchSources as Sources

------------------------------------------------------------------------
-- Shared abstract dynamics for language denoising and perceptual completion.
--
-- The state labels are not proposed neural atoms.  They encode three regimes:
-- underdetermined input, a geometric/intermediate organisation, and a strongly
-- semantically bound interpretation.  Different precision landscapes select
-- different fixed points from the same state space.
------------------------------------------------------------------------

attractorSources : List Sources.ResearchSource
attractorSources =
  Sources.nieLargeLanguageDiffusion ∷
  Sources.pengPlannerAwarePathLearning ∷
  Sources.carhartHarrisLSDNeuroimaging ∷
  Sources.singletonControlLandscape ∷
  Sources.bressloffGeometricHallucinations ∷ []

data CompletionState : Set where
  noisyUnderdetermined
  geometricIntermediate
  semanticCompletion : CompletionState

commitmentOf : CompletionState → BT.Trit
commitmentOf noisyUnderdetermined = BT.zero
commitmentOf geometricIntermediate = BT.zero
commitmentOf semanticCompletion = BT.pos

------------------------------------------------------------------------
-- Ordinary high-precision completion rapidly selects a semantic basin.
------------------------------------------------------------------------

ordinaryDenoise : CompletionState → CompletionState
ordinaryDenoise noisyUnderdetermined = semanticCompletion
ordinaryDenoise geometricIntermediate = semanticCompletion
ordinaryDenoise semanticCompletion = semanticCompletion

ordinaryNoiseCompletesSemantically :
  ordinaryDenoise noisyUnderdetermined ≡ semanticCompletion
ordinaryNoiseCompletesSemantically = refl

semanticCompletionIsOrdinaryFixedPoint :
  ordinaryDenoise semanticCompletion ≡ semanticCompletion
semanticCompletionIsOrdinaryFixedPoint = refl

------------------------------------------------------------------------
-- Reduced semantic precision allows the geometric intermediate to persist.
------------------------------------------------------------------------

reducedSemanticDenoise : CompletionState → CompletionState
reducedSemanticDenoise noisyUnderdetermined = geometricIntermediate
reducedSemanticDenoise geometricIntermediate = geometricIntermediate
reducedSemanticDenoise semanticCompletion = geometricIntermediate

noiseEntersGeometricIntermediate :
  reducedSemanticDenoise noisyUnderdetermined ≡ geometricIntermediate
noiseEntersGeometricIntermediate = refl

geometricIntermediateIsReducedPrecisionFixedPoint :
  reducedSemanticDenoise geometricIntermediate ≡ geometricIntermediate
geometricIntermediateIsReducedPrecisionFixedPoint = refl

geometricIntermediateRemainsProjective :
  commitmentOf geometricIntermediate ≡ BT.zero
geometricIntermediateRemainsProjective = refl

------------------------------------------------------------------------
-- Basis + noise + defect energy landscapes.
--
-- The values are finite structural fixtures.  They make explicit that increased
-- entropy/freedom does not mean equal energy for every state: the operator and
-- boundary conditions still make selected modes cheap.
------------------------------------------------------------------------

record CompletionEnergy : Set where
  constructor completionEnergy
  field
    basisCost : Nat
    noiseCost : Nat
    bindingDefect : Nat

open CompletionEnergy public

totalEnergy : CompletionEnergy → Nat
totalEnergy energy = basisCost energy + noiseCost energy + bindingDefect energy
  where
  _+_ : Nat → Nat → Nat
  zero + right = right
  suc left + right = suc (left + right)

ordinaryEnergy : CompletionState → CompletionEnergy
ordinaryEnergy noisyUnderdetermined = completionEnergy 1 6 2
ordinaryEnergy geometricIntermediate = completionEnergy 2 1 2
ordinaryEnergy semanticCompletion = completionEnergy 2 0 0

reducedSemanticEnergy : CompletionState → CompletionEnergy
reducedSemanticEnergy noisyUnderdetermined = completionEnergy 1 6 2
reducedSemanticEnergy geometricIntermediate = completionEnergy 2 0 0
reducedSemanticEnergy semanticCompletion = completionEnergy 2 0 3

ordinarySemanticEnergyIsTwo :
  totalEnergy (ordinaryEnergy semanticCompletion) ≡ 2
ordinarySemanticEnergyIsTwo = refl

ordinaryGeometricEnergyIsFive :
  totalEnergy (ordinaryEnergy geometricIntermediate) ≡ 5
ordinaryGeometricEnergyIsFive = refl

reducedGeometricEnergyIsTwo :
  totalEnergy (reducedSemanticEnergy geometricIntermediate) ≡ 2
reducedGeometricEnergyIsTwo = refl

reducedSemanticEnergyIsFive :
  totalEnergy (reducedSemanticEnergy semanticCompletion) ≡ 5
reducedSemanticEnergyIsFive = refl

geometricWinsReducedPrecisionLandscape :
  totalEnergy (reducedSemanticEnergy geometricIntermediate)
  ≤ totalEnergy (reducedSemanticEnergy semanticCompletion)
geometricWinsReducedPrecisionLandscape = s≤s (s≤s z≤n)

semanticWinsOrdinaryLandscape :
  totalEnergy (ordinaryEnergy semanticCompletion)
  ≤ totalEnergy (ordinaryEnergy geometricIntermediate)
semanticWinsOrdinaryLandscape = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Residence-time fixture.
------------------------------------------------------------------------

ordinaryTrajectory : List CompletionState
ordinaryTrajectory = noisyUnderdetermined ∷ semanticCompletion ∷ []

reducedPrecisionTrajectory : List CompletionState
reducedPrecisionTrajectory =
  noisyUnderdetermined ∷
  geometricIntermediate ∷
  geometricIntermediate ∷
  semanticCompletion ∷ []

countGeometric : List CompletionState → Nat
countGeometric [] = 0
countGeometric (geometricIntermediate ∷ rest) = suc (countGeometric rest)
countGeometric (_ ∷ rest) = countGeometric rest

ordinaryGeometricResidenceIsZero : countGeometric ordinaryTrajectory ≡ 0
ordinaryGeometricResidenceIsZero = refl

reducedPrecisionGeometricResidenceIsTwo :
  countGeometric reducedPrecisionTrajectory ≡ 2
reducedPrecisionGeometricResidenceIsTwo = refl
