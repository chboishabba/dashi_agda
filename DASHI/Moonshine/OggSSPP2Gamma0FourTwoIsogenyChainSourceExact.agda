module DASHI.Moonshine.OggSSPP2Gamma0FourTwoIsogenyChainSourceExact where

------------------------------------------------------------------------
-- p=2 GAMMA_0(4) INTERIOR SOURCE AS TWO DEGREE-2 ISOGENY STEPS
--
-- DASHI CONTRIBUTION
--
-- A cyclic rank-4 subgroup C4 with rank-2 subflag C2 can be exposed
-- source-facing as a length-two chain of degree-2 quotient morphisms:
--
--     E0 --phi1--> E1 --phi2--> E2
--
-- together with a witness that the composite kernel is the selected rank-4
-- Gamma_0(4) subgroup and the first-step kernel is its selected rank-2 subflag.
--
-- This module is an interface/equivalence target, not an inhabited arithmetic
-- construction.  It is deliberately agnostic about how the finite-flat
-- subgroup schemes and quotients are implemented internally.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Gamma0
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record DegreeTwoIsogenyStep : Set₁ where
  field
    SourceCurve : Set
    TargetCurve : Set
    Kernel : Set

    source : SourceCurve
    target : TargetCurve

    degree : Nat
    degreeIsTwo : degree ≡ 2

    kernelRank : Nat
    kernelRankIsTwo : kernelRank ≡ 2

    finiteFlatKernel : Bool
    finiteFlatKernelIsTrue :
      finiteFlatKernel ≡ true

open DegreeTwoIsogenyStep public

record Gamma0FourTwoIsogenyChain : Set₁ where
  field
    E0 E1 E2 : Set
    K1 K2 KComposite : Set

    firstStep :
      DegreeTwoIsogenyStep

    secondStep :
      DegreeTwoIsogenyStep

    middleCurveMatches :
      TargetCurve firstStep ≡ SourceCurve secondStep

    compositeKernelRank : Nat
    compositeKernelRankIsFour :
      compositeKernelRank ≡ 4

    firstKernelIsOrderTwoSubflag : Bool
    firstKernelIsOrderTwoSubflagIsTrue :
      firstKernelIsOrderTwoSubflag ≡ true

    compositeKernelIsGamma0FourCyclic : Bool
    compositeKernelIsGamma0FourCyclicIsTrue :
      compositeKernelIsGamma0FourCyclic ≡ true

    characteristicTwoBadPrimeSemantics : Bool
    characteristicTwoBadPrimeSemanticsIsTrue :
      characteristicTwoBadPrimeSemantics ≡ true

    sourceReference : String

open Gamma0FourTwoIsogenyChain public

record ChainToSubgroupDatumRecognition
  (chain : Gamma0FourTwoIsogenyChain) : Set₁ where
  field
    subgroupDatum :
      Gamma0.Gamma0FourFiniteFlatDatum

    firstStepKernelMatchesSubflag : Bool
    firstStepKernelMatchesSubflagIsTrue :
      firstStepKernelMatchesSubflag ≡ true

    compositeKernelMatchesOrderFourSubgroup : Bool
    compositeKernelMatchesOrderFourSubgroupIsTrue :
      compositeKernelMatchesOrderFourSubgroup ≡ true

open ChainToSubgroupDatumRecognition public

data TwoDegreeTwoStepsAutomaticallyGiveCyclicGamma0Four : Set where
data CompositeDegreeFourAutomaticallyGivesCyclicKernel : Set where

twoDegreeTwoStepsDoNotAutomaticallyGiveCyclicGamma0Four :
  TwoDegreeTwoStepsAutomaticallyGiveCyclicGamma0Four -> ⊥
twoDegreeTwoStepsDoNotAutomaticallyGiveCyclicGamma0Four ()

degreeFourCompositeDoesNotAutomaticallyGiveCyclicKernel :
  CompositeDegreeFourAutomaticallyGivesCyclicKernel -> ⊥
degreeFourCompositeDoesNotAutomaticallyGiveCyclicKernel ()

data TwoIsogenyChainResidual : Set where
  missingFirstFiniteFlatDegreeTwoStep :
    TwoIsogenyChainResidual
  missingSecondFiniteFlatDegreeTwoStep :
    TwoIsogenyChainResidual
  missingCompositeCyclicityWitness :
    TwoIsogenyChainResidual
  missingSubflagCompatibility :
    TwoIsogenyChainResidual
  missingFrobeniusTransportOnChain :
    TwoIsogenyChainResidual

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Gamma0FourTwoIsogenyChainBoundary : Set where
  constructor gamma0-four-two-isogeny-chain-boundary
  field
    twoStepPresentationTyped : Bool
    eachStepDegreeTwoRequired : Bool
    compositeRankFourRequired : Bool
    compositeCyclicityStillExplicitWitness : Bool
    orderTwoSubflagStillExplicitWitness : Bool
    arithmeticChainConstructed : Bool
    firstResidual : TwoIsogenyChainResidual

canonicalGamma0FourTwoIsogenyChainBoundary :
  Gamma0FourTwoIsogenyChainBoundary
canonicalGamma0FourTwoIsogenyChainBoundary =
  gamma0-four-two-isogeny-chain-boundary
    true true true true true false
    missingFirstFiniteFlatDegreeTwoStep
