{-# OPTIONS --safe #-}
module DASHI.Unified.Fleet58ManifestAcquisitionExact where

------------------------------------------------------------------------
-- FLEET 58 NAMED-MANIFEST ACQUISITION MAX-CUT
--
-- This module starts after DASHI.Unified.FleetFormalGapTOEExact.
-- The counted partition is paid.
-- The named 58-row formal-gap manifest is not checked in.
--
-- O. Organization.
-- DASHI TOE / Fleet residual proving frontier.
--
-- R. Requirement.
-- Bind the missing named manifest to the generic exact-live acquisition
-- carrier. Reuse the existing Fleet and Ibrahim Pareto/snowball owners.
--
-- C. Code.
-- One bound acquisition demand. No synthetic gap row is constructed.
--
-- S. State.
-- 584 discharged fibres remain closed.
-- 44 contradiction gaps remain separate.
-- 58 is a count only until the named manifest arrives.
--
-- L. Lattice.
-- ITIR Fleet source store -> named manifest acquisition -> per-gap referee
-- discovery -> reuse/unify/extend/construct.
--
-- P. Proposal.
-- Stop before per-gap formalisation while the manifest is absent.
--
-- G. Governance.
-- Search priority is not proof. Acquisition is not discharge.
-- Equal cardinality is not same-object identity.
--
-- F. Follow-up.
-- Acquire the named manifest. Then run related_symbols, discover, and
-- round_lineage for each named gap before any new theorem construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Unified.FleetFormalGapTOEExact as Fleet
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Pareto

------------------------------------------------------------------------
-- Exact acquisition coordinates.
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
-- Current fail-closed state.
------------------------------------------------------------------------

named58ManifestAcquired : Bool
named58ManifestAcquired =
  Fleet.namedFormalGapManifestAcquired
    Fleet.canonicalFleetFormalGapMaxCut

named58ManifestAcquiredIsFalse :
  named58ManifestAcquired ≡ false
named58ManifestAcquiredIsFalse =
  Fleet.namedFormalGapManifestAcquiredIsFalse
    Fleet.canonicalFleetFormalGapMaxCut

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
relatedSymbolsRequired =
  Fleet.relatedSymbolsRequiredBeforeConstruction
    Fleet.canonicalFleetFormalGapMaxCut

relatedSymbolsRequiredIsTrue :
  relatedSymbolsRequired ≡ true
relatedSymbolsRequiredIsTrue =
  Fleet.relatedSymbolsRequiredBeforeConstructionIsTrue
    Fleet.canonicalFleetFormalGapMaxCut

discoverRequired : Bool
discoverRequired =
  Fleet.discoverRequiredBeforeConstruction
    Fleet.canonicalFleetFormalGapMaxCut

discoverRequiredIsTrue :
  discoverRequired ≡ true
discoverRequiredIsTrue =
  Fleet.discoverRequiredBeforeConstructionIsTrue
    Fleet.canonicalFleetFormalGapMaxCut

roundLineageRequired : Bool
roundLineageRequired =
  Fleet.roundLineageRequiredBeforeConstruction
    Fleet.canonicalFleetFormalGapMaxCut

roundLineageRequiredIsTrue :
  roundLineageRequired ≡ true
roundLineageRequiredIsTrue =
  Fleet.roundLineageRequiredBeforeConstructionIsTrue
    Fleet.canonicalFleetFormalGapMaxCut

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
-- Existing non-promotion theorems.
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
  Pareto.SearchPriorityCreatesProof → ⊥
searchPriorityDoesNotCreateProof =
  Pareto.searchPriorityDoesNotCreateProof

data Count58CreatesNamedRows : Set where

count58DoesNotCreateNamedRows :
  Count58CreatesNamedRows → ⊥
count58DoesNotCreateNamedRows ()

------------------------------------------------------------------------
-- Attribution and boundary receipt.
------------------------------------------------------------------------

record Fleet58ManifestAcquisitionReceipt : Set₁ where
  constructor fleet58-manifest-acquisition-receipt
  field
    fleetReceipt : Fleet.FleetFormalGapTOEReceipt
    fleetMaxCut : Fleet.FleetFormalGapMaxCut
    boundDemand :
      Bound.BoundAcquisitionDemand
        manifestAlignment
        named58FormalGapManifest
        unnamed58FormalGapIdentities

    sourceRepository : String
    sourcePath : String

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
    Fleet.canonicalFleetFormalGapReceipt
    Fleet.canonicalFleetFormalGapMaxCut
    manifestAcquisitionDemand
    Fleet.fleetSourceRepository
    Fleet.fleetSourcePath
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

------------------------------------------------------------------------
-- Attribution statement.
------------------------------------------------------------------------

attributionBoundary : String
attributionBoundary =
  "ITIR-suite owns the Fleet R4/R5 execution and planning receipt. Existing DASHI theorem owners retain proof authority. Tadeusz Bałaban and cited source authors retain mathematical attribution. Ibrahim/Danforth/Dodds and existing Monster/source owners retain their attribution. casey-git-clone, zkSEC, zkperf, zos-server, erdfa-py, and aristotle-cli-rs retain separate authorship and authority. This module imports no theorem authority from those repositories."
