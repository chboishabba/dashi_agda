module DASHI.Biology.Psychedelic5HT2AAttentionBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources

------------------------------------------------------------------------
-- 5-HT2A / ATTENTION-SALIENCE BOUNDARY
--
-- SOURCE CLAIMS:
--
-- * Beliveau et al. provide a human in-vivo serotonin receptor atlas including
--   5-HT2A.
-- * Preller et al. 2017 use ketanserin blockade to support a 5-HT2A-dependent
--   component of LSD subjective effects and personal-relevance processing.
-- * Preller et al. 2018 support a 5-HT2A-dependent component of LSD-related
--   global/thalamic connectivity changes.
-- * Ham et al. study dACC/insula as a salience-network system.
-- * Cipolotti et al. provide a recent caution against treating ACC activation
--   as a simple necessary executive controller across canonical tasks.
--
-- DASHI EXTENSION:
--
-- The composition of those claims into a candidate
--
--   5-HT2A perturbation
--     -> altered relevance/salience weighting
--     -> increased attentional capture of endogenous visual content
--
-- is represented below as a typed hypothesis surface.  No cited source is
-- attributed the whole composite mechanism.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

data MechanismLayer : Set where
  receptorAvailability : MechanismLayer
  pharmacologicalDependence : MechanismLayer
  networkReconfiguration : MechanismLayer
  salienceControlAssociation : MechanismLayer
  phenomenalImperative : MechanismLayer
  entityCommunicationInterpretation : MechanismLayer

record SourcePaidMechanismLayer : Set where
  constructor sourcePaidMechanismLayer
  field
    layer : MechanismLayer
    source : Source.AttributedSource
    importedRole : String

open SourcePaidMechanismLayer public

human5HT2AAtlasLayer : SourcePaidMechanismLayer
human5HT2AAtlasLayer =
  sourcePaidMechanismLayer
    receptorAvailability
    Sources.beliveauEtAl2017
    "Human in-vivo receptor mapping supports distributed 5-HT2A availability; anatomy alone does not prove psychedelic causal flow."

lsdSubjectiveBlockadeLayer : SourcePaidMechanismLayer
lsdSubjectiveBlockadeLayer =
  sourcePaidMechanismLayer
    pharmacologicalDependence
    Sources.prellerEtAl2017
    "Ketanserin blockade supports a 5-HT2A-dependent component of measured LSD subjective and personal-relevance effects."

lsdConnectivityBlockadeLayer : SourcePaidMechanismLayer
lsdConnectivityBlockadeLayer =
  sourcePaidMechanismLayer
    networkReconfiguration
    Sources.prellerEtAl2018
    "Ketanserin blockade supports a 5-HT2A-dependent component of measured LSD-related global/thalamic connectivity changes."

daccSalienceLayer : SourcePaidMechanismLayer
daccSalienceLayer =
  sourcePaidMechanismLayer
    salienceControlAssociation
    Sources.hamEtAl2013
    "dACC and bilateral insula are treated as salience-network nodes in the cited effective-connectivity study."

accCautionLayer : SourcePaidMechanismLayer
accCautionLayer =
  sourcePaidMechanismLayer
    salienceControlAssociation
    Sources.cipolottiEtAl2025
    "ACC activation is not promoted to a simple necessary executive-control mechanism; the source is used as an anti-overclaim constraint."

------------------------------------------------------------------------
-- Candidate cross-layer composition.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  sourceSupported : EvidenceStatus
  dashiCompositeCandidate : EvidenceStatus
  notEstablished : EvidenceStatus

record PsychedelicSalienceComposition : Set where
  constructor psychedelicSalienceComposition
  field
    receptorLayer : SourcePaidMechanismLayer
    blockadeLayer : SourcePaidMechanismLayer
    connectivityLayer : SourcePaidMechanismLayer
    salienceLayer : SourcePaidMechanismLayer
    cautionLayer : SourcePaidMechanismLayer

    receptorToSubjectiveDependence : EvidenceStatus
    receptorToNetworkReconfiguration : EvidenceStatus

    networkToAlteredSalienceWeighting : EvidenceStatus
    alteredSalienceToEndogenousCapture : EvidenceStatus
    endogenousCaptureToImperativeMeaning : EvidenceStatus
    imperativeMeaningToEntityCommunication : EvidenceStatus

open PsychedelicSalienceComposition public

canonicalPsychedelicSalienceComposition :
  PsychedelicSalienceComposition
canonicalPsychedelicSalienceComposition =
  psychedelicSalienceComposition
    human5HT2AAtlasLayer
    lsdSubjectiveBlockadeLayer
    lsdConnectivityBlockadeLayer
    daccSalienceLayer
    accCautionLayer
    sourceSupported
    sourceSupported
    dashiCompositeCandidate
    dashiCompositeCandidate
    notEstablished
    notEstablished

------------------------------------------------------------------------
-- Exact non-promotion surface.
------------------------------------------------------------------------

data ACC5HT2AProvesImperativeAttention : Set where

data ACC5HT2AProvesEntityCommunication : Set where

data ReceptorMapProvesPhenomenalMeaning : Set where

acc5HT2ADoesNotProveImperativeAttention :
  ACC5HT2AProvesImperativeAttention → ⊥
acc5HT2ADoesNotProveImperativeAttention ()

acc5HT2ADoesNotProveEntityCommunication :
  ACC5HT2AProvesEntityCommunication → ⊥
acc5HT2ADoesNotProveEntityCommunication ()

receptorMapDoesNotProvePhenomenalMeaning :
  ReceptorMapProvesPhenomenalMeaning → ⊥
receptorMapDoesNotProvePhenomenalMeaning ()

record Psychedelic5HT2AAttentionBoundary : Set where
  constructor psychedelic5HT2AAttentionBoundary
  field
    human5HT2AMappingSourceBound : Bool
    human5HT2AMappingSourceBoundIsTrue :
      human5HT2AMappingSourceBound ≡ true

    controlledLSD5HT2ADependenceSourceBound : Bool
    controlledLSD5HT2ADependenceSourceBoundIsTrue :
      controlledLSD5HT2ADependenceSourceBound ≡ true

    daccSalienceAssociationSourceBound : Bool
    daccSalienceAssociationSourceBoundIsTrue :
      daccSalienceAssociationSourceBound ≡ true

    alteredSalienceCompositionIsCandidate : Bool
    alteredSalienceCompositionIsCandidateIsTrue :
      alteredSalienceCompositionIsCandidate ≡ true

    accIsUniquePsychedelicAttentionController : Bool
    accIsUniquePsychedelicAttentionControllerIsFalse :
      accIsUniquePsychedelicAttentionController ≡ false

    imperativeLookAtThisMechanismEstablished : Bool
    imperativeLookAtThisMechanismEstablishedIsFalse :
      imperativeLookAtThisMechanismEstablished ≡ false

    telepathicEntitySignalEstablished : Bool
    telepathicEntitySignalEstablishedIsFalse :
      telepathicEntitySignalEstablished ≡ false

    oneReceptorExplainsCompleteExperience : Bool
    oneReceptorExplainsCompleteExperienceIsFalse :
      oneReceptorExplainsCompleteExperience ≡ false

open Psychedelic5HT2AAttentionBoundary public

canonicalPsychedelic5HT2AAttentionBoundary :
  Psychedelic5HT2AAttentionBoundary
canonicalPsychedelic5HT2AAttentionBoundary =
  psychedelic5HT2AAttentionBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
