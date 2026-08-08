module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Give the dependency-ordered lemma ladder from the literal periodic Clay
-- contract to a submission witness.  The states are intentionally fail-closed:
--
--   exactTarget          -- part of Fefferman alternative (B);
--   checkedExact         -- exact mathematics already proved in repository;
--   checkedReducer       -- composition works once physical inputs exist;
--   physicalProducerOpen -- load-bearing PDE/analysis still unproved;
--   sourceAuditOpen      -- a claimed-paper step still needs full audit.
--
-- This module does not count filenames or receipts as mathematical progress.
-- A lane advances only when a physicalProducerOpen field becomes a checked
-- theorem, or when an exact counterexample narrows or rejects the proposed
-- statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as EndToEnd


data LemmaState : Set where
  exactTarget : LemmaState
  checkedExact : LemmaState
  checkedReducer : LemmaState
  physicalProducerOpen : LemmaState
  sourceAuditOpen : LemmaState

record HighestAlphaClayLemmaLadder : Set where
  constructor highestAlphaClayLemmaLadder
  field
    -- L0--L2: exact target and local continuation envelope.
    L0_literalFeffermanPeriodicAlternativeB : LemmaState
    L1_periodicMeanCenteringAndGalileanRestoration : LemmaState
    L2_localCriticalWellPosednessMaximalTimeRestart : LemmaState

    -- L3--L6: actual finite Fourier/Galerkin equation and damping.
    L3_periodicDivergenceFreeGalerkinFourierCarrier : LemmaState
    L4_exhaustiveBonyAndCommutatorSupportPartition : LemmaState
    L5_finiteFilteredVorticityEnstrophyIdentity : LemmaState
    L6_pairInputFrequencyDiffusionCoercivity : LemmaState

    -- L7--L14: load-bearing nonlinear taxation.
    L7_fivePhysicalSourceBoundsUniformInCutoffs : LemmaState
    L8_periodicPrincipalValueStrainKernelSphereCancellationCZ : LemmaState
    L9_continuumIncrementToDiffusionCoercivity : LemmaState
    L10_farFieldAnnularPackingOrCarlesonBound : LemmaState
    L11_criticalCommutatorAndSubgridStressBound : LemmaState
    L12_hystereticPositiveVariationBound : LemmaState
    L13_dissipationWavenumberHighModeAndLowReservoirBound : LemmaState
    L14_uniformGeometricResidualTailRatio : LemmaState

    -- L15--L17: one strict critical budget.
    L15_strictTotalViscosityTaxBelowOne : LemmaState
    L16_uniformIntegratedCriticalEnergyInequality : LemmaState
    L17_continuousGronwallWithoutTargetNormOnRight : LemmaState

    -- L18--L22: physical limits and continuation.
    L18_shellCutoffConvergence : LemmaState
    L19_galerkinCutoffConvergenceStrongEnoughForNonlinearity : LemmaState
    L20_lowerSemicontinuityPreservesAbsorbedBudget : LemmaState
    L21_pressureSmoothnessRecoveryAndCriticalRestart : LemmaState
    L22_arbitraryMeanGalileanUncentering : LemmaState

    -- L23: exact terminal composition.
    L23_literalFeffermanWitnessAndAuditComposition : LemmaState

open HighestAlphaClayLemmaLadder public

canonicalHighestAlphaClayLemmaLadder : HighestAlphaClayLemmaLadder
canonicalHighestAlphaClayLemmaLadder =
  highestAlphaClayLemmaLadder
    exactTarget
    checkedReducer
    checkedReducer
    physicalProducerOpen
    checkedExact
    checkedExact
    checkedExact
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer

------------------------------------------------------------------------
-- Existing terminal theorem: after the path inputs are inhabited, no further
-- wrapper or promotion lemma is required.
------------------------------------------------------------------------

highestAlphaPathInputsGiveLiteralClayB :
  ∀ {legacy clay} →
  EndToEnd.InRepoClayPathInputs legacy clay →
  Clay.FeffermanPeriodicClayStatementB clay
highestAlphaPathInputsGiveLiteralClayB =
  EndToEnd.inRepoPathClosesLiteralFeffermanPeriodicB

record HighestAlphaRound24AuthorityBoundary : Set where
  constructor highestAlphaRound24AuthorityBoundary
  field
    exactTargetRepresented : Bool
    exactDependencyOrderRepresented : Bool
    terminalCompositionAlreadyClosed : Bool
    claimedPaperCorpusCanSupplyAuthorityWithoutAudit : Bool
    allPhysicalProducersInhabited : Bool
    unconditionalClayTheoremPromoted : Bool

canonicalHighestAlphaRound24AuthorityBoundary :
  HighestAlphaRound24AuthorityBoundary
canonicalHighestAlphaRound24AuthorityBoundary =
  highestAlphaRound24AuthorityBoundary
    true true true false false false
