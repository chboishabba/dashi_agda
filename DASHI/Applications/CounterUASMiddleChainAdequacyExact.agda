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
-- classifications, threat assessments, authority and response.  This module
-- adds only the missing query-indexed separation between classification and
-- threat assessment.  No sensing, targeting, mitigation, waveform, frequency,
-- power or defeat procedure is introduced here.
------------------------------------------------------------------------

classifiedUASCreatesHostility : Bool
classifiedUASCreatesHostility = false

fusionConfidenceCreatesHostility : Bool
fusionConfidenceCreatesHostility = false

middleChainCreatesMitigationAuthority : Bool
middleChainCreatesMitigationAuthority = false

------------------------------------------------------------------------
-- Exact collision:
-- two worlds expose the same classified-UAS surface while differing in the
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
