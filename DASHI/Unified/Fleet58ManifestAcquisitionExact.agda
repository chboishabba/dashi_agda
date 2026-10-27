{-# OPTIONS --safe #-}
module DASHI.Unified.Fleet58ManifestAcquisitionExact where

------------------------------------------------------------------------
-- FLEET 58 NAMED-MANIFEST ACQUISITION MAX-CUT
--
-- The canonical Fleet owner pays the recorded 584 / 44 / 58 partition.
-- It does not provide 58 named gap identities.
-- This module binds that missing artifact to the generic acquisition carrier.
-- It constructs no synthetic gap row.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Pareto

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F
--
-- O. DASHI TOE Fleet formal-gap frontier.
-- R. Reuse Fleet, BoundAcquisitionDemand, and Ibrahim Pareto/snowball.
-- C. Bind one exact acquisition route for the missing named manifest.
-- S. 584 stays discharged. 44 stays contradiction-only. 58 stays count-only.
-- L. source store -> manifest -> referee -> reuse/unify/extend/construct.
-- P. Per-gap dispatch is disabled until a named manifest is acquired.
-- G. Acquisition is not proof. Search priority is not proof.
-- F. The external named-manifest artifact is the current wall.
------------------------------------------------------------------------

data ManifestRequirement : Set where
  named58FormalGapManifest : ManifestRequirement

data ManifestResidual : Set where
  unnamed58FormalGapIdentities : ManifestResidual

data ManifestProducer : Set where
  itirFleetSourceStore : ManifestProducer

data ManifestAcquisition : Set where
  acquireNamed58Manifest : ManifestAcquisition

manifestAlignment :
  Bound.AcquisitionAlignment
    ManifestRequirement
    ManifestResidual
    ManifestProducer
    ManifestAcquisition
manifestAlignment =
  Bound.acquisition-alignment
    (λ _ → unnamed58FormalGapIdentities)
    (λ _ → itirFleetSourceStore)
    (λ _ → unnamed58FormalGapIdentities)
    (λ _ → itirFleetSourceStore)

manifestAcquisitionDemand :
  Bound.BoundAcquisitionDemand
    manifestAlignment
    named58FormalGapManifest
    unnamed58FormalGapIdentities
manifestAcquisitionDemand =
  Bound.bound-acquisition-demand
    acquireNamed58Manifest
    refl
    refl
    refl

manifestAcquisitionPaysSelectedResidual :
  Bound.acquisitionResidual
    manifestAlignment
    (Bound.acquisition manifestAcquisitionDemand)
  ≡
  Bound.residualForRequirement
    manifestAlignment
    named58FormalGapManifest
manifestAcquisitionPaysSelectedResidual =
  Bound.acquisitionPaysSelectedResidual manifestAcquisitionDemand

manifestAcquisitionUsesSelectedProducer :
  Bound.acquisitionProducer
    manifestAlignment
    (Bound.acquisition manifestAcquisitionDemand)
  ≡
  Bound.producerForRequirement
    manifestAlignment
    named58FormalGapManifest
manifestAcquisitionUsesSelectedProducer =
  Bound.acquisitionUsesSelectedProducer manifestAcquisitionDemand

------------------------------------------------------------------------
-- Canonical recorded Fleet partition.
------------------------------------------------------------------------

fleetRecordedDischargedCount : Nat
fleetRecordedDischargedCount =
  Fleet.dischargedCoreKnowledgeFibres
    Fleet.canonicalFleetFormalGapTargetReceipt

fleetRecordedDischargedCountIs584 :
  fleetRecordedDischargedCount ≡ 584
fleetRecordedDischargedCountIs584 =
  Fleet.fleetRecordedDischargedCountIs584

fleetRecordedContradictionCount : Nat
fleetRecordedContradictionCount =
  Fleet.polarityContradictionGaps
    Fleet.canonicalFleetFormalGapTargetReceipt

fleetRecordedContradictionCountIs44 :
  fleetRecordedContradictionCount ≡ 44
fleetRecordedContradictionCountIs44 =
  Fleet.fleetRecordedContradictionCountIs44

fleetRecordedFormalGapCount : Nat
fleetRecordedFormalGapCount =
  Fleet.unformalisedFormalGaps
    Fleet.canonicalFleetFormalGapTargetReceipt

fleetRecordedFormalGapCountIs58 :
  fleetRecordedFormalGapCount ≡ 58
fleetRecordedFormalGapCountIs58 =
  Fleet.fleetRecordedUnformalisedGapCountIs58

fleetTargetsOnlyFormalGapClass :
  Fleet.targetOnlyUnformalisedFormalGaps
    Fleet.canonicalFleetFormalGapTargetReceipt
  ≡ true
fleetTargetsOnlyFormalGapClass =
  Fleet.fleetTargetsOnlyUnformalisedFormalGaps

fleetDischargedClassRemainsClosed :
  Fleet.dischargedFibresRemainDischarged
    Fleet.canonicalFleetFormalGapTargetReceipt
  ≡ true
fleetDischargedClassRemainsClosed =
  Fleet.fleetDoesNotRetargetDischargedFibres

fleetContradictionClassRemainsSeparate :
  Fleet.contradictionGapsRemainSeparate
    Fleet.canonicalFleetFormalGapTargetReceipt
  ≡ true
fleetContradictionClassRemainsSeparate =
  Fleet.fleetKeepsContradictionsSeparate

------------------------------------------------------------------------
-- Current manifest state.
--
-- This is a repository/intake state coordinate.
-- It does not assert that no such artifact exists outside checked-in sources.
------------------------------------------------------------------------

named58ManifestAcquired : Bool
named58ManifestAcquired = false

named58ManifestAcquiredIsFalse :
  named58ManifestAcquired ≡ false
named58ManifestAcquiredIsFalse = refl

perGapDispatchEnabled : Bool
perGapDispatchEnabled = false

perGapDispatchEnabledIsFalse :
  perGapDispatchEnabled ≡ false
perGapDispatchEnabledIsFalse = refl

manifestAcquisitionRouteBound : Bool
manifestAcquisitionRouteBound = true

manifestAcquisitionRouteBoundIsTrue :
  manifestAcquisitionRouteBound ≡ true
manifestAcquisitionRouteBoundIsTrue = refl

relatedSymbolsRequired : Bool
relatedSymbolsRequired = true

relatedSymbolsRequiredIsTrue :
  relatedSymbolsRequired ≡ true
relatedSymbolsRequiredIsTrue = refl

discoverRequired : Bool
discoverRequired = true

discoverRequiredIsTrue :
  discoverRequired ≡ true
discoverRequiredIsTrue = refl

roundLineageRequired : Bool
roundLineageRequired = true

roundLineageRequiredIsTrue :
  roundLineageRequired ≡ true
roundLineageRequiredIsTrue = refl

SearchPriorityCreatesProof : Set
SearchPriorityCreatesProof =
  Pareto.SearchPriorityCreatesProof

searchPriorityCreatesProof : Bool
searchPriorityCreatesProof = false

searchPriorityCreatesProofIsFalse :
  searchPriorityCreatesProof ≡ false
searchPriorityCreatesProofIsFalse = refl

esdSurfaceEdited : Bool
esdSurfaceEdited = false

esdSurfaceEditedIsFalse :
  esdSurfaceEdited ≡ false
esdSurfaceEditedIsFalse = refl

------------------------------------------------------------------------
-- Non-promotion.
------------------------------------------------------------------------

acquisitionDoesNotPayRequirement :
  Bound.BoundDemandAutomaticallyPaysRequirement → ⊥
acquisitionDoesNotPayRequirement =
  Bound.bindingDoesNotPayRequirement

acquisitionDoesNotCloseConsumer :
  Bound.BoundDemandAutomaticallyClosesConsumer → ⊥
acquisitionDoesNotCloseConsumer =
  Bound.bindingDoesNotCloseConsumer

producerDoesNotIdentifyResidual :
  Bound.SameProducerIdentifiesResidual → ⊥
producerDoesNotIdentifyResidual =
  Bound.producerIdentityDoesNotIdentifyResidual

searchPriorityDoesNotCreateProof :
  SearchPriorityCreatesProof → ⊥
searchPriorityDoesNotCreateProof =
  Pareto.searchPriorityDoesNotCreateProof

data Count58CreatesNamedRows : Set where

count58DoesNotCreateNamedRows :
  Count58CreatesNamedRows → ⊥
count58DoesNotCreateNamedRows ()

------------------------------------------------------------------------
-- Canonical receipt.
------------------------------------------------------------------------

record Fleet58ManifestAcquisitionReceipt : Set₁ where
  constructor fleet58-manifest-acquisition-receipt
  field
    fleetReceipt : Fleet.FleetFormalGapTargetReceipt
    boundDemand :
      Bound.BoundAcquisitionDemand
        manifestAlignment
        named58FormalGapManifest
        unnamed58FormalGapIdentities

    sourceRepository : String
    sourceSurface : String

    recordedDischargedCount : Nat
    recordedDischargedCountIs584 : recordedDischargedCount ≡ 584
    recordedContradictionCount : Nat
    recordedContradictionCountIs44 : recordedContradictionCount ≡ 44
    recordedFormalGapCount : Nat
    recordedFormalGapCountIs58 : recordedFormalGapCount ≡ 58

    manifestPresent : Bool
    manifestPresentIsFalse : manifestPresent ≡ false
    perGapDispatch : Bool
    perGapDispatchIsFalse : perGapDispatch ≡ false

    requiresRelatedSymbols : Bool
    requiresRelatedSymbolsIsTrue : requiresRelatedSymbols ≡ true
    requiresDiscover : Bool
    requiresDiscoverIsTrue : requiresDiscover ≡ true
    requiresRoundLineage : Bool
    requiresRoundLineageIsTrue : requiresRoundLineage ≡ true

    metaIntrospectorTheoremAuthorityImported : Bool
    metaIntrospectorTheoremAuthorityImportedIsFalse :
      metaIntrospectorTheoremAuthorityImported ≡ false

    esdEdited : Bool
    esdEditedIsFalse : esdEdited ≡ false

open Fleet58ManifestAcquisitionReceipt public

canonicalFleet58ManifestAcquisitionReceipt :
  Fleet58ManifestAcquisitionReceipt
canonicalFleet58ManifestAcquisitionReceipt =
  fleet58-manifest-acquisition-receipt
    Fleet.canonicalFleetFormalGapTargetReceipt
    manifestAcquisitionDemand
    (Fleet.externalSourceRepository
      Fleet.canonicalFleetFormalGapTargetReceipt)
    (Fleet.externalSourceSurface
      Fleet.canonicalFleetFormalGapTargetReceipt)
    fleetRecordedDischargedCount
    fleetRecordedDischargedCountIs584
    fleetRecordedContradictionCount
    fleetRecordedContradictionCountIs44
    fleetRecordedFormalGapCount
    fleetRecordedFormalGapCountIs58
    named58ManifestAcquired
    named58ManifestAcquiredIsFalse
    perGapDispatchEnabled
    perGapDispatchEnabledIsFalse
    relatedSymbolsRequired
    relatedSymbolsRequiredIsTrue
    discoverRequired
    discoverRequiredIsTrue
    roundLineageRequired
    roundLineageRequiredIsTrue
    false
    refl
    esdSurfaceEdited
    esdSurfaceEditedIsFalse

attributionBoundary : String
attributionBoundary =
  "ITIR-suite owns the Fleet R4/R5 execution and planning receipt. Existing DASHI theorem owners retain proof authority. Tadeusz Bałaban and cited source authors retain mathematical attribution. Ibrahim/Danforth/Dodds and existing Monster/source owners retain attribution. casey-git-clone, zkSEC, zkperf, zos-server, erdfa-py, and aristotle-cli-rs retain separate authorship and authority. No theorem authority is imported from those repositories by this module."
