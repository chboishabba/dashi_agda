{-# OPTIONS --safe #-}
module DASHI.Unified.Fleet58ManifestAcquisitionExact where

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
-- Fleet 58 named-manifest acquisition boundary.
--
-- The Fleet owner records 584 discharged fibres, 44 contradiction gaps,
-- and 58 unformalised formal gaps.
-- It does not contain the 58 row identities.
-- This owner binds the exact missing artifact.
-- It creates no synthetic gap row.
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
-- Reuse the canonical Fleet partition.
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

------------------------------------------------------------------------
-- Current source-controlled manifest state.
--
-- The checked repository state contains the count and graph identity.
-- It does not contain an immutable export of the 58 named rows.
-- This coordinate says nothing about unqueried external database state.
------------------------------------------------------------------------

named58ManifestAcquired : Bool
named58ManifestAcquired = false

named58ManifestAcquiredIsFalse :
  named58ManifestAcquired ≡ false
named58ManifestAcquiredIsFalse = refl

countIdentifiesNamedRows : Bool
countIdentifiesNamedRows = false

countIdentifiesNamedRowsIsFalse :
  countIdentifiesNamedRows ≡ false
countIdentifiesNamedRowsIsFalse = refl

perGapDispatchEnabled : Bool
perGapDispatchEnabled = named58ManifestAcquired

perGapDispatchEnabledIsFalse :
  perGapDispatchEnabled ≡ false
perGapDispatchEnabledIsFalse =
  named58ManifestAcquiredIsFalse

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
-- Reused non-promotion theorems.
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

SearchPriorityCreatesProof : Set
SearchPriorityCreatesProof =
  Pareto.SearchPriorityCreatesProof

searchPriorityDoesNotCreateProof :
  SearchPriorityCreatesProof → ⊥
searchPriorityDoesNotCreateProof =
  Pareto.searchPriorityDoesNotCreateProof

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
    sourceDocumentGraphIdentity : String

    recordedDischargedCount : Nat
    recordedDischargedCountIs584 : recordedDischargedCount ≡ 584
    recordedContradictionCount : Nat
    recordedContradictionCountIs44 : recordedContradictionCount ≡ 44
    recordedFormalGapCount : Nat
    recordedFormalGapCountIs58 : recordedFormalGapCount ≡ 58

    manifestPresent : Bool
    manifestPresentIsFalse : manifestPresent ≡ false
    countNamesRows : Bool
    countNamesRowsIsFalse : countNamesRows ≡ false
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
    "pnf-document-graph:d14f740cb5ec4b39f22998832691f5932bae5e527118280f648f607b57456fc7"
    fleetRecordedDischargedCount
    fleetRecordedDischargedCountIs584
    fleetRecordedContradictionCount
    fleetRecordedContradictionCountIs44
    fleetRecordedFormalGapCount
    fleetRecordedFormalGapCountIs58
    named58ManifestAcquired
    named58ManifestAcquiredIsFalse
    countIdentifiesNamedRows
    countIdentifiesNamedRowsIsFalse
    perGapDispatchEnabled
    perGapDispatchEnabledIsFalse
    manifestAcquisitionRouteBound
    manifestAcquisitionRouteBoundIsTrue
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

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F.
------------------------------------------------------------------------

canonicalFleet58ManifestZKPFrame : Pareto.TOEZKPFrame
canonicalFleet58ManifestZKPFrame =
  Pareto.toe-zkp-frame
    "acquire an immutable named manifest for the 58 Fleet formal gaps before per-gap dispatch"
    "reuse FleetFormalGapTargetTOEExact, BoundAcquisitionDemandExact, and Ibrahim Pareto/snowball"
    "bind one exact acquisition demand; create no synthetic row and no duplicate Fleet owner"
    "584 stays discharged; 44 stays separate; 58 stays count-only until the manifest arrives"
    "one source-store-to-manifest acquisition lane"
    "the source-controlled count and graph identity are present; the 58 row identities are not"
    "acquisition is not proof; search priority is not proof; meta-introspector and ESD theorem authority is not imported"
    "manifest present enables per-gap dispatch; absent manifest keeps dispatch false"
    "after acquisition run related_symbols, discover, and round_lineage before reuse, unify, extend, or construct"
    false
    false
    false
    false

attributionBoundary : String
attributionBoundary =
  "ITIR-suite owns the Fleet R4/R5 execution and planning receipt. Existing DASHI theorem owners retain proof authority. Tadeusz Balaban and cited source authors retain mathematical attribution. Ibrahim/Danforth/Dodds and existing Monster/source owners retain attribution. casey-git-clone, zkSEC, zkperf, zos-server, erdfa-py, and aristotle-cli-rs retain separate authorship and authority. No theorem authority is imported from those repositories by this module."
