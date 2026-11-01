module DASHI.Applications.CounterUASMiddleChainAdequacyExact where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASDroneShieldExact as CUAS
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- COUNTER-UAS MIDDLE-CHAIN ADEQUACY
--
-- Thin application boundary for the already-typed middle of the defensive
-- chain:
--   association/fusion -> classification/track -> threat assessment.
--
-- CounterUASDroneShieldExact remains the owner of observations, fused tracks,
-- classifications, threat assessments, authority and response. This module
-- adds only the missing query-indexed separations for association provenance
-- and classification-to-threat adequacy. No sensing, targeting, mitigation,
-- waveform, frequency, power or defeat procedure is introduced here.
------------------------------------------------------------------------

fusedObservationsCreateSameObjectAssociation : Bool
fusedObservationsCreateSameObjectAssociation = false

classifiedUASCreatesHostility : Bool
classifiedUASCreatesHostility = false

fusionConfidenceCreatesHostility : Bool
fusionConfidenceCreatesHostility = false

middleChainCreatesMitigationAuthority : Bool
middleChainCreatesMitigationAuthority = false

------------------------------------------------------------------------
-- I. Observation/fusion surface is inadequate for same-object association.
--
-- The same visible observation set can be assigned either to one paid
-- same-object lineage or to an unresolved/cross-object association hypothesis.
-- Fusion does not manufacture association identity merely by co-locating inputs.
------------------------------------------------------------------------

data AssociationWorld : Set where
  sameObjectAssociationWorld : AssociationWorld
  unresolvedAssociationWorld : AssociationWorld

data ObservationSurface : Set where
  sameVisibleObservationSet : ObservationSurface

data AssociationLineageSurface : Set where
  sameObjectLineagePaid : AssociationLineageSurface
  associationLineageUnresolved : AssociationLineageSurface

data AssociationQuery : Set where
  observationVisibilityQuery : AssociationQuery
  associationStatusQuery : AssociationQuery

data AssociationAnswer : Set where
  observationsVisible : AssociationAnswer
  associationPaid : AssociationAnswer
  associationUnresolved : AssociationAnswer

observationSurfaceProjection : AssociationWorld → ObservationSurface
observationSurfaceProjection world = sameVisibleObservationSet

associationLineageProjection : AssociationWorld → AssociationLineageSurface
associationLineageProjection sameObjectAssociationWorld = sameObjectLineagePaid
associationLineageProjection unresolvedAssociationWorld = associationLineageUnresolved

associationAnswer : AssociationQuery → AssociationWorld → AssociationAnswer
associationAnswer observationVisibilityQuery world = observationsVisible
associationAnswer associationStatusQuery sameObjectAssociationWorld = associationPaid
associationAnswer associationStatusQuery unresolvedAssociationWorld = associationUnresolved

associationSemantics :
  Adequacy.QuerySemantics AssociationWorld AssociationQuery AssociationAnswer
associationSemantics = Adequacy.querySemantics associationAnswer

observationSurfaceAssociationAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    observationSurfaceProjection
    associationSemantics
    associationStatusQuery
observationSurfaceAssociationAdequacyDefect =
  Adequacy.queryAdequacyDefect
    sameObjectAssociationWorld
    unresolvedAssociationWorld
    refl
    (λ ())

observationSurfaceCannotDetermineAssociation :
  Adequacy.AdequateFor
    observationSurfaceProjection
    associationSemantics
    associationStatusQuery →
  ⊥
observationSurfaceCannotDetermineAssociation =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    observationSurfaceAssociationAdequacyDefect

observationAndAssociationProjection :
  AssociationWorld → ObservationSurface × AssociationLineageSurface
observationAndAssociationProjection =
  Observer.pairObserver observationSurfaceProjection associationLineageProjection

joinedAssociationAnswer :
  ObservationSurface × AssociationLineageSurface → AssociationAnswer
joinedAssociationAnswer (sameVisibleObservationSet , sameObjectLineagePaid) = associationPaid
joinedAssociationAnswer (sameVisibleObservationSet , associationLineageUnresolved) = associationUnresolved

observationAndAssociationDetermineAssociation :
  Adequacy.AdequateFor
    observationAndAssociationProjection
    associationSemantics
    associationStatusQuery
observationAndAssociationDetermineAssociation =
  Adequacy.factorsForQuery
    joinedAssociationAnswer
    (λ { sameObjectAssociationWorld → refl
       ; unresolvedAssociationWorld → refl
       })

observationAndAssociationStrictlyRefinesObservationSurface :
  Observer.StrictRefinement
    observationSurfaceProjection
    observationAndAssociationProjection
observationAndAssociationStrictlyRefinesObservationSurface =
  Observer.strictPairRefinement
    observationSurfaceProjection
    associationLineageProjection
    sameObjectAssociationWorld
    unresolvedAssociationWorld
    refl
    (λ ())

------------------------------------------------------------------------
-- II. Classification surface is inadequate for threat assessment.
--
-- Two worlds expose the same classified-UAS surface while differing in the
-- operational/threat context relevant to the threat-assessment consumer.
------------------------------------------------------------------------

data MiddleChainWorld : Set where
  classifiedUASBenignContext : MiddleChainWorld
  classifiedUASThreatContext : MiddleChainWorld

data ThreatContextSurface : Set where
  benignContextSurface : ThreatContextSurface
  threatContextSurface : ThreatContextSurface

data ThreatQuery : Set where
  classificationQuery : ThreatQuery
  threatAssessmentQuery : ThreatQuery

data ThreatAnswer : Set where
  classifiedUASObserved : ThreatAnswer
  noHostilityEstablished : ThreatAnswer
  hostilityEstablished : ThreatAnswer

classificationOnlyProjection : MiddleChainWorld → CUAS.ClassificationState
classificationOnlyProjection classifiedUASBenignContext = CUAS.classifiedUAS
classificationOnlyProjection classifiedUASThreatContext = CUAS.classifiedUAS

threatContextProjection : MiddleChainWorld → ThreatContextSurface
threatContextProjection classifiedUASBenignContext = benignContextSurface
threatContextProjection classifiedUASThreatContext = threatContextSurface

threatAnswer : ThreatQuery → MiddleChainWorld → ThreatAnswer
threatAnswer classificationQuery world = classifiedUASObserved
threatAnswer threatAssessmentQuery classifiedUASBenignContext = noHostilityEstablished
threatAnswer threatAssessmentQuery classifiedUASThreatContext = hostilityEstablished

threatSemantics :
  Adequacy.QuerySemantics MiddleChainWorld ThreatQuery ThreatAnswer
threatSemantics = Adequacy.querySemantics threatAnswer

classificationOnlyThreatAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    classificationOnlyProjection
    threatSemantics
    threatAssessmentQuery
classificationOnlyThreatAdequacyDefect =
  Adequacy.queryAdequacyDefect
    classifiedUASBenignContext
    classifiedUASThreatContext
    refl
    (λ ())

classificationOnlyCannotDetermineThreat :
  Adequacy.AdequateFor
    classificationOnlyProjection
    threatSemantics
    threatAssessmentQuery →
  ⊥
classificationOnlyCannotDetermineThreat =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    classificationOnlyThreatAdequacyDefect

------------------------------------------------------------------------
-- Constructive local refinement: classification + threat-relevant context.
------------------------------------------------------------------------

classificationAndContextProjection :
  MiddleChainWorld → CUAS.ClassificationState × ThreatContextSurface
classificationAndContextProjection =
  Observer.pairObserver classificationOnlyProjection threatContextProjection

joinedThreatAnswer :
  CUAS.ClassificationState × ThreatContextSurface → ThreatAnswer
joinedThreatAnswer (CUAS.classifiedUAS , benignContextSurface) = noHostilityEstablished
joinedThreatAnswer (CUAS.classifiedUAS , threatContextSurface) = hostilityEstablished
joinedThreatAnswer (_ , benignContextSurface) = noHostilityEstablished
joinedThreatAnswer (_ , threatContextSurface) = hostilityEstablished

classificationAndContextDetermineThreat :
  Adequacy.AdequateFor
    classificationAndContextProjection
    threatSemantics
    threatAssessmentQuery
classificationAndContextDetermineThreat =
  Adequacy.factorsForQuery
    joinedThreatAnswer
    (λ { classifiedUASBenignContext → refl
       ; classifiedUASThreatContext → refl
       })

classificationAndContextStrictlyRefinesClassification :
  Observer.StrictRefinement
    classificationOnlyProjection
    classificationAndContextProjection
classificationAndContextStrictlyRefinesClassification =
  Observer.strictPairRefinement
    classificationOnlyProjection
    threatContextProjection
    classifiedUASBenignContext
    classifiedUASThreatContext
    refl
    (λ ())

record CounterUASMiddleChainBoundary : Set where
  constructor counterUASMiddleChainBoundary
  field
    fusedObservationSetEqualsSameObjectAssociation : Bool
    fusedObservationSetEqualsSameObjectAssociationIsFalse :
      fusedObservationSetEqualsSameObjectAssociation ≡ false
    classificationEqualsHostility : Bool
    classificationEqualsHostilityIsFalse : classificationEqualsHostility ≡ false
    fusionConfidenceEqualsHostility : Bool
    fusionConfidenceEqualsHostilityIsFalse : fusionConfidenceEqualsHostility ≡ false
    middleChainEqualsMitigationAuthority : Bool
    middleChainEqualsMitigationAuthorityIsFalse :
      middleChainEqualsMitigationAuthority ≡ false

canonicalCounterUASMiddleChainBoundary : CounterUASMiddleChainBoundary
canonicalCounterUASMiddleChainBoundary =
  counterUASMiddleChainBoundary
    false refl
    false refl
    false refl
    false refl
