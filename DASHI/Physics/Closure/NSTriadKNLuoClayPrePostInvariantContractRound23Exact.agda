module DASHI.Physics.Closure.NSTriadKNLuoClayPrePostInvariantContractRound23Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
--
-- Give one normalized control surface for the exact Clay preconditions,
-- postconditions, proof-route invariants and remaining analytic producers.
-- A clause marked exactTarget is present in the literal Fefferman theorem type.
-- A clause marked checkedReducer has a repository theorem that transports the
-- required evidence once its physical inputs are supplied.  A clause marked
-- physicalProducerOpen is still load-bearing mathematics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact
import DASHI.Physics.Closure.NSTriadKNLuoPairFrequencyDefectDiffusionExact
import DASHI.Physics.Closure.NSTriadKNLuoFiveSourceDefectCriticalTaxExact
import DASHI.Physics.Closure.NSTriadKNLuoCriticalProductionGronwallClosureExact
import DASHI.Physics.Closure.NSTriadKNLuoNestedGalerkinShellLimitExact
import DASHI.Physics.Closure.NSTriadKNLuoCriticalRestartContradictionExact
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact

data RequirementState : Set where
  exactTarget checkedReducer physicalProducerOpen : RequirementState

record ClayPreconditions : Set where
  constructor clayPreconditions
  field
    arbitraryPositiveViscosity : RequirementState
    dimensionExactlyThree : RequirementState
    spatialDomainUnitThreeTorus : RequirementState
    externalForceIdenticallyZero : RequirementState
    arbitrarySmoothDatum : RequirementState
    datumDivergenceFree : RequirementState
    datumUnitPeriodic : RequirementState
    datumMeanZeroNotRequired : RequirementState

open ClayPreconditions public

canonicalClayPreconditions : ClayPreconditions
canonicalClayPreconditions =
  clayPreconditions
    exactTarget exactTarget exactTarget exactTarget
    exactTarget exactTarget exactTarget exactTarget

record ClayPostconditions : Set where
  constructor clayPostconditions
  field
    velocityExistsForAllNonnegativeTime : RequirementState
    pressureExistsForAllNonnegativeTime : RequirementState
    velocitySmoothGlobally : RequirementState
    pressureSmoothGlobally : RequirementState
    velocityUnitPeriodic : RequirementState
    pressureUnitPeriodicErratum : RequirementState
    momentumEquationWithViscosityAndZeroForce : RequirementState
    incompressibilityAtEveryTime : RequirementState
    initialTraceAtTimeZero : RequirementState
    uniquenessNotPartOfOfficialAlternativeB : RequirementState
    periodicEnergyBoundNotPartOfOfficialAlternativeB : RequirementState

open ClayPostconditions public

canonicalClayPostconditions : ClayPostconditions
canonicalClayPostconditions =
  clayPostconditions
    exactTarget exactTarget exactTarget exactTarget exactTarget exactTarget
    exactTarget exactTarget exactTarget exactTarget exactTarget

record ProofRouteInvariants : Set where
  constructor proofRouteInvariants
  field
    GalerkinDivergenceFreePreserved : RequirementState
    periodicTranslationStructurePreserved : RequirementState
    shellAndGalerkinConstantsUniform : RequirementState
    NavierStokesCriticalScalingPreserved : RequirementState
    fivePhysicalSourcesExhaustive : RequirementState
    pairInputFrequencyDampingRetained : RequirementState
    positiveCriticalProductionOnlyTaxed : RequirementState
    totalViscosityTaxStrictlyBelowOne : RequirementState
    noUncontrolledCriticalSupremumOnRight : RequirementState
    noBKMNormAssumedOnRight : RequirementState
    noAlignmentOrResidenceHypothesisAssumed : RequirementState
    centeredMeanRestoredByGalileanTransform : RequirementState
    pressurePeriodicityRecovered : RequirementState
    nonlinearTermsAbsorbedBeforeWeakLimit : RequirementState
    shellThenGalerkinLimitOrderPreserved : RequirementState
    boundedCriticalNormFeedsRestart : RequirementState

open ProofRouteInvariants public

canonicalProofRouteInvariants : ProofRouteInvariants
canonicalProofRouteInvariants =
  proofRouteInvariants
    checkedReducer checkedReducer physicalProducerOpen physicalProducerOpen
    physicalProducerOpen checkedReducer checkedReducer physicalProducerOpen
    checkedReducer checkedReducer checkedReducer physicalProducerOpen
    physicalProducerOpen checkedReducer checkedReducer checkedReducer

record InRepoPathState : Set where
  constructor inRepoPathState
  field
    literalFeffermanTheoremType : RequirementState
    finiteGalerkinEnstrophyIdentity : RequirementState
    pairFrequencyDiffusionRepair : RequirementState
    fiveSourceTaxAlgebra : RequirementState
    physicalFiveSourceUniformTax : RequirementState
    hystereticPositiveVariationEstimate : RequirementState
    dissipationWavenumberHighModeEstimate : RequirementState
    lowFrequencyCriticalReservoirEstimate : RequirementState
    periodicPrincipalValueKernelAndCZ : RequirementState
    continuumIncrementToDiffusionCoercivity : RequirementState
    uniformResidualTailRatios : RequirementState
    strictCombinedCoefficient : RequirementState
    continuousGronwall : RequirementState
    analyticShellConvergence : RequirementState
    analyticGalerkinConvergence : RequirementState
    localCriticalRestartTheorem : RequirementState
    pressureAndSmoothnessRecovery : RequirementState
    arbitraryMeanGalileanReduction : RequirementState
    literalPhysicalCarrierAdapter : RequirementState
    unconditionalClayTheorem : RequirementState

open InRepoPathState public

canonicalInRepoPathState : InRepoPathState
canonicalInRepoPathState =
  inRepoPathState
    exactTarget
    checkedReducer
    checkedReducer
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen

record ClayContractAuthorityBoundary : Set where
  constructor clayContractAuthorityBoundary
  field
    exactPreconditionSurfaceImplemented : Bool
    exactPostconditionSurfaceImplemented : Bool
    proofRouteInvariantSurfaceImplemented : Bool
    existingReducersConnected : Bool
    allPhysicalProducersInhabited : Bool
    unconditionalClayTheoremPromoted : Bool

open ClayContractAuthorityBoundary public

canonicalClayContractAuthorityBoundary : ClayContractAuthorityBoundary
canonicalClayContractAuthorityBoundary =
  clayContractAuthorityBoundary true true true true false false

clayContractSurfaceImplemented : Bool
clayContractSurfaceImplemented = true

clayContractSurfaceImplementedIsTrue :
  clayContractSurfaceImplemented ≡ true
clayContractSurfaceImplementedIsTrue = refl

clayPhysicalProducersRemainOpen :
  allPhysicalProducersInhabited canonicalClayContractAuthorityBoundary
  ≡ false
clayPhysicalProducersRemainOpen = refl
