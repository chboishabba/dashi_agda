module DASHI.Applications.CounterUASSensibLawAuthorityBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASDroneShieldExact as CUAS
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Law.SensibLawInternationalInstrumentLifecycleExact as Lifecycle
import DASHI.Law.SensibLawCCWLAWS2026Exact as CCW2026

------------------------------------------------------------------------
-- COUNTER-UAS / SENSIBLAW AUTHORITY BRIDGE
--
-- This is deliberately thin.  Domestic mitigation authority, armed-conflict
-- context, LAWS classification and international-law applicability are
-- independent coordinates.  The bridge does not assert that every counter-UAS
-- event is an armed-conflict event or a LAWS event.
------------------------------------------------------------------------

record CounterUASLegalContext : Set where
  constructor counterUASLegalContext
  field
    domesticAuthority : CUAS.AuthorityState
    instrumentLifecycle : Lifecycle.InstrumentLifecycleSnapshot
    armedConflictContextEstablished : Bool
    lawsClassificationEstablished : Bool
    internationalLawApplicabilityEstablished : Bool

open CounterUASLegalContext public

september2026ReferenceContext : CounterUASLegalContext
september2026ReferenceContext =
  counterUASLegalContext
    CUAS.noMitigationAuthority
    CCW2026.september2026LifecycleSnapshot
    false
    false
    false

------------------------------------------------------------------------
-- Query-indexed collision:
-- identical domestic mitigation authority cannot determine international-law
-- applicability because the latter depends on independent legal/factual state.
------------------------------------------------------------------------

data LegalContextWorld : Set where
  sameDomesticAuthorityNoInternationalApplicability : LegalContextWorld
  sameDomesticAuthorityWithInternationalApplicability : LegalContextWorld

data DomesticAuthoritySurface : Set where
  sameDomesticMitigationGrant : DomesticAuthoritySurface

data LegalContextQuery : Set where
  domesticAuthorityQuery : LegalContextQuery
  internationalApplicabilityQuery : LegalContextQuery

data LegalContextAnswer : Set where
  domesticAuthorityObserved : LegalContextAnswer
  internationalApplicabilityNotEstablished : LegalContextAnswer
  internationalApplicabilityEstablished : LegalContextAnswer

domesticAuthorityOnlyProjection : LegalContextWorld → DomesticAuthoritySurface
domesticAuthorityOnlyProjection world = sameDomesticMitigationGrant

legalContextAnswer : LegalContextQuery → LegalContextWorld → LegalContextAnswer
legalContextAnswer domesticAuthorityQuery world = domesticAuthorityObserved
legalContextAnswer internationalApplicabilityQuery sameDomesticAuthorityNoInternationalApplicability =
  internationalApplicabilityNotEstablished
legalContextAnswer internationalApplicabilityQuery sameDomesticAuthorityWithInternationalApplicability =
  internationalApplicabilityEstablished

legalContextSemantics :
  Adequacy.QuerySemantics LegalContextWorld LegalContextQuery LegalContextAnswer
legalContextSemantics = Adequacy.querySemantics legalContextAnswer

domesticAuthorityOnlyApplicabilityAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    domesticAuthorityOnlyProjection
    legalContextSemantics
    internationalApplicabilityQuery
domesticAuthorityOnlyApplicabilityAdequacyDefect =
  Adequacy.queryAdequacyDefect
    sameDomesticAuthorityNoInternationalApplicability
    sameDomesticAuthorityWithInternationalApplicability
    refl
    (λ ())

domesticAuthorityOnlyCannotDetermineInternationalApplicability :
  Adequacy.AdequateFor
    domesticAuthorityOnlyProjection
    legalContextSemantics
    internationalApplicabilityQuery →
  ⊥
domesticAuthorityOnlyCannotDetermineInternationalApplicability =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    domesticAuthorityOnlyApplicabilityAdequacyDefect

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

domesticMitigationAuthorityDoesNotCreateInternationalLawApplicability : Bool
domesticMitigationAuthorityDoesNotCreateInternationalLawApplicability = true

domesticMitigationAuthorityDoesNotCreateArmedConflictStatus : Bool
domesticMitigationAuthorityDoesNotCreateArmedConflictStatus = true

domesticMitigationAuthorityDoesNotCreateLAWSClassification : Bool
domesticMitigationAuthorityDoesNotCreateLAWSClassification = true

technicalAutonomyDoesNotCreateLawfulAutonomousEngagement : Bool
technicalAutonomyDoesNotCreateLawfulAutonomousEngagement = true

threatAssessmentDoesNotCreateInternationalLawApplicability : Bool
threatAssessmentDoesNotCreateInternationalLawApplicability = true

ccwConsensusElementsDoNotCreateDomesticMitigationAuthority : Bool
ccwConsensusElementsDoNotCreateDomesticMitigationAuthority = true

counterUASEventDoesNotAutomaticallyInstantiateLAWS : Bool
counterUASEventDoesNotAutomaticallyInstantiateLAWS = true
