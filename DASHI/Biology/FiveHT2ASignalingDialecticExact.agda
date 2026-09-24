module DASHI.Biology.FiveHT2ASignalingDialecticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources
import DASHI.Biology.Kluver5HT2AMolecularProteinInstantiationExact as Molecular
import DASHI.Biology.NeurochemicalTransmissionBridge as Transmission
import DASHI.Biology.NeurochemicalProteinTargetBridge as ProteinTarget

------------------------------------------------------------------------
-- SOURCE-CONDITIONED 5-HT2A SIGNALING DIALECTIC
--
-- The repo must not flatten apparently competing primary results:
--
--   Wallach et al. 2023:
--     Gq efficacy / Gq-PLC disruption tracks mouse head-twitch response in
--     their ligand series and assay.
--
--   Xu et al. 2026:
--     non-canonical Gi signaling is essential in their hallucinogenic-effect
--     assays and they resolve 5-HT2A-Gi/Gq complexes structurally.
--
-- These are retained as source-conditioned observations over different
-- experimental surfaces.  DASHI does not adjudicate them into one universal
-- pathway theorem.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

data FiveHT2ATransducer : Set where
  gq11 : FiveHT2ATransducer
  gi : FiveHT2ATransducer
  betaArrestin2 : FiveHT2ATransducer

data DownstreamCoordinate : Set where
  plcCoordinate : DownstreamCoordinate
  calciumCoordinate : DownstreamCoordinate
  arrestinRecruitmentCoordinate : DownstreamCoordinate
  receptorInternalizationCoordinate : DownstreamCoordinate
  giEffectorCoordinate : DownstreamCoordinate
  transcriptionalCoordinate : DownstreamCoordinate
  neuralExcitabilityCoordinate : DownstreamCoordinate

data AssayDomain : Set where
  inVitroBRETAssay : AssayDomain
  calciumFluxAssay : AssayDomain
  mouseHeadTwitchAssay : AssayDomain
  mouseBehavioralAssay : AssayDomain
  cryoEMStructuralAssay : AssayDomain
  humanSubjectiveAssay : AssayDomain
  humanNeuroimagingAssay : AssayDomain

data EvidenceRelation : Set where
  predictsWithinAssay : EvidenceRelation
  attenuatesWithinAssay : EvidenceRelation
  structurallyObserved : EvidenceRelation
  associatedWithinAssay : EvidenceRelation
  necessaryInReportedAssay : EvidenceRelation
  insufficientByItself : EvidenceRelation
  unresolvedAcrossDomains : EvidenceRelation

record SourceConditionedSignalingClaim : Set where
  constructor sourceConditionedSignalingClaim
  field
    source : Source.AttributedSource
    transducer : FiveHT2ATransducer
    downstream : DownstreamCoordinate
    assay : AssayDomain
    relation : EvidenceRelation
    reading : String

    universalHumanMechanism : Bool
    universalHumanMechanismIsFalse :
      universalHumanMechanism ≡ false

open SourceConditionedSignalingClaim public

wallachGqHTR : SourceConditionedSignalingClaim
wallachGqHTR =
  sourceConditionedSignalingClaim
    Sources.wallachEtAl2023
    gq11
    plcCoordinate
    mouseHeadTwitchAssay
    predictsWithinAssay
    "In the tested ligand series, 5-HT2A Gq efficacy tracked HTR magnitude and perturbing Gq/PLC attenuated HTR."
    false refl

wallachArrestinHTR : SourceConditionedSignalingClaim
wallachArrestinHTR =
  sourceConditionedSignalingClaim
    Sources.wallachEtAl2023
    betaArrestin2
    arrestinRecruitmentCoordinate
    mouseHeadTwitchAssay
    insufficientByItself
    "Beta-arrestin2 recruitment did not track HTR magnitude in the tested series and beta-arrestin-biased agonists lacked HTR under the reported conditions."
    false refl

xuGiHallucinogenicAssay : SourceConditionedSignalingClaim
xuGiHallucinogenicAssay =
  sourceConditionedSignalingClaim
    Sources.xuEtAl2026
    gi
    giEffectorCoordinate
    mouseBehavioralAssay
    necessaryInReportedAssay
    "The source reports non-canonical 5-HT2A-mediated Gi signaling as essential in its hallucinogenic-effect assay surface."
    false refl

xuGiStructure : SourceConditionedSignalingClaim
xuGiStructure =
  sourceConditionedSignalingClaim
    Sources.xuEtAl2026
    gi
    giEffectorCoordinate
    cryoEMStructuralAssay
    structurallyObserved
    "The source reports 5-HT2A-Gi complexes bound to psychedelic ligands."
    false refl

xuGqStructure : SourceConditionedSignalingClaim
xuGqStructure =
  sourceConditionedSignalingClaim
    Sources.xuEtAl2026
    gq11
    plcCoordinate
    cryoEMStructuralAssay
    structurallyObserved
    "The source also reports 5-HT2A-Gq structural complexes, preserving multi-transducer receptor-state structure."
    false refl

canonicalSourceConditionedSignalingClaims :
  List SourceConditionedSignalingClaim
canonicalSourceConditionedSignalingClaims =
  wallachGqHTR
  ∷ wallachArrestinHTR
  ∷ xuGiHallucinogenicAssay
  ∷ xuGiStructure
  ∷ xuGqStructure
  ∷ []

------------------------------------------------------------------------
-- Ligand -> receptor state -> signaling profile.
------------------------------------------------------------------------

record SignalingProfile : Set where
  constructor signalingProfile
  field
    ligand : Molecular.MolecularIdentityReceipt

    gqCoordinate : EvidenceRelation
    giCoordinate : EvidenceRelation
    betaArrestinCoordinate : EvidenceRelation

    profileIsAssayIndexed : Bool
    profileIsAssayIndexedIsTrue :
      profileIsAssayIndexed ≡ true

    profileIsSingleScalar : Bool
    profileIsSingleScalarIsFalse :
      profileIsSingleScalar ≡ false

open SignalingProfile public

lsdSignalingProfile : SignalingProfile
lsdSignalingProfile =
  signalingProfile
    Molecular.lsdIdentity
    associatedWithinAssay
    associatedWithinAssay
    associatedWithinAssay
    true refl
    false refl

------------------------------------------------------------------------
-- Existing repo owner reuse.
------------------------------------------------------------------------

proteinTargetBridge :
  ProteinTarget.NeurochemicalProteinTargetBridge
proteinTargetBridge =
  ProteinTarget.canonicalNeurochemicalProteinTargetBridge

neurochemicalTransmissionBridge :
  Transmission.NeurochemicalTransmissionBridge
neurochemicalTransmissionBridge =
  Transmission.canonicalNeurochemicalTransmissionBridge

proteinTargetSupportsConformationCandidate :
  List ProteinTarget.ProteinTargetActionCandidate
proteinTargetSupportsConformationCandidate =
  ProteinTarget.canonicalProteinTargetActionCandidates

transmissionSupportsOccupancyAndEncoding :
  List Transmission.NeurochemicalTransmissionCarrier
transmissionSupportsOccupancyAndEncoding =
  Transmission.canonicalNeurochemicalTransmissionCarriers

------------------------------------------------------------------------
-- DASHI cross-source synthesis.
------------------------------------------------------------------------

data UniversalGqOnlyMechanism : Set where
data UniversalGiOnlyMechanism : Set where
data BetaArrestinAloneExplainsPsychedelicEffect : Set where
data StructuralStateAloneDeterminesPhenomenology : Set where

universalGqOnlyMechanismBlocked :
  UniversalGqOnlyMechanism → ⊥
universalGqOnlyMechanismBlocked ()

universalGiOnlyMechanismBlocked :
  UniversalGiOnlyMechanism → ⊥
universalGiOnlyMechanismBlocked ()

betaArrestinAloneMechanismBlocked :
  BetaArrestinAloneExplainsPsychedelicEffect → ⊥
betaArrestinAloneMechanismBlocked ()

structureAloneDoesNotDeterminePhenomenology :
  StructuralStateAloneDeterminesPhenomenology → ⊥
structureAloneDoesNotDeterminePhenomenology ()

record FiveHT2ASignalingDialectic : Set where
  constructor fiveHT2ASignalingDialectic
  field
    sourceConditionedClaims :
      List SourceConditionedSignalingClaim

    lsdProfile :
      SignalingProfile

    gqEvidenceRetained : Bool
    gqEvidenceRetainedIsTrue :
      gqEvidenceRetained ≡ true

    giEvidenceRetained : Bool
    giEvidenceRetainedIsTrue :
      giEvidenceRetained ≡ true

    arrestinEvidenceRetained : Bool
    arrestinEvidenceRetainedIsTrue :
      arrestinEvidenceRetained ≡ true

    oneUniversalTransducerSelected : Bool
    oneUniversalTransducerSelectedIsFalse :
      oneUniversalTransducerSelected ≡ false

    assayDomainMatters : Bool
    assayDomainMattersIsTrue :
      assayDomainMatters ≡ true

    humanPhenomenologyMechanismClosed : Bool
    humanPhenomenologyMechanismClosedIsFalse :
      humanPhenomenologyMechanismClosed ≡ false

open FiveHT2ASignalingDialectic public

canonicalFiveHT2ASignalingDialectic :
  FiveHT2ASignalingDialectic
canonicalFiveHT2ASignalingDialectic =
  fiveHT2ASignalingDialectic
    canonicalSourceConditionedSignalingClaims
    lsdSignalingProfile
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Exact mechanistic frontier.
------------------------------------------------------------------------

record FiveHT2ASignalingFrontier : Set where
  constructor fiveHT2ASignalingFrontier
  field
    paid : String
    missing : String
    nextHighestAlphaWeld : String

canonicalFiveHT2ASignalingFrontier : FiveHT2ASignalingFrontier
canonicalFiveHT2ASignalingFrontier =
  fiveHT2ASignalingFrontier
    "source-conditioned Gq/PLC, Gi, beta-arrestin2 and receptor-structure coordinates are represented without collapsing experimental domains"
    "same-ligand same-assay quantitative transducer amplitudes linked to concentration/occupancy, cell type, circuit response and visual-cortical mode"
    "instantiate a protocol-indexed transducer vector and transport it through receptor occupancy -> neural encoding -> visual-circuit perturbation while preserving source/assay identity"
