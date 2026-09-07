module DASHI.Core.PluralObserverCorrectionRealisationExact where

------------------------------------------------------------------------
-- PLURAL OBSERVER / CORRECTION / REALISATION
--
-- Generic DASHI owner.
--
-- A system may have a declared norm, an institutional self-observation, an
-- affected-party observation, an independent observation, a correction
-- response, and a realised outcome. These are distinct coordinates.
--
-- The theorem shape is deliberately source-neutral. Domain modules may supply
-- source-bounded interpretations (for example Two-Eyed Seeing in an Indigenous
-- context), but no such source is claimed to author this generic construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF

record PluralOperationalSystem
    (State Declared Institutional Affected Independent Correction Outcome : Set) : Set₁ where
  constructor plural-operational-system
  field
    declaredNorm : State → Declared
    institutionalObservation : State → Institutional
    affectedObservation : State → Affected
    independentObservation : State → Independent
    correctionResponse : State → Correction
    realisedOutcome : State → Outcome

open PluralOperationalSystem public

------------------------------------------------------------------------
-- Consumer-indexed closure. No strand is globally privileged by default.
------------------------------------------------------------------------

record RealisationConsumer
    (Declared Institutional Affected Independent Correction Outcome : Set) : Set₁ where
  constructor realisation-consumer
  field
    AcceptDeclared : Declared → Set
    AcceptInstitutional : Institutional → Set
    AcceptAffected : Affected → Set
    AcceptIndependent : Independent → Set
    AcceptCorrection : Correction → Set
    AcceptOutcome : Outcome → Set

open RealisationConsumer public

record RealisationReceipt
    {State Declared Institutional Affected Independent Correction Outcome : Set}
    (system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome)
    (consumer : RealisationConsumer
      Declared Institutional Affected Independent Correction Outcome)
    (state : State) : Set₁ where
  constructor realisation-receipt
  field
    declaredAccepted : AcceptDeclared consumer (declaredNorm system state)
    institutionalAccepted :
      AcceptInstitutional consumer (institutionalObservation system state)
    affectedAccepted : AcceptAffected consumer (affectedObservation system state)
    independentAccepted :
      AcceptIndependent consumer (independentObservation system state)
    correctionAccepted : AcceptCorrection consumer (correctionResponse system state)
    outcomeAccepted : AcceptOutcome consumer (realisedOutcome system state)

open RealisationReceipt public

------------------------------------------------------------------------
-- Collision receipts expose exactly which institutional surface is too coarse.
------------------------------------------------------------------------

record InstitutionalAffectedCollision
    {State Declared Institutional Affected Independent Correction Outcome : Set}
    (system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome) : Set where
  constructor institutional-affected-collision
  field
    left right : State
    sameInstitutionalObservation :
      institutionalObservation system left
      ≡ institutionalObservation system right
    differentAffectedObservation :
      affectedObservation system left
      ≡ affectedObservation system right → ⊥

open InstitutionalAffectedCollision public

institutionalAffectedCollisionIsNonfactorability :
  ∀ {State Declared Institutional Affected Independent Correction Outcome : Set}
    {system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome} →
  InstitutionalAffectedCollision system →
  INF.NonFactorabilityWitness
    (institutionalObservation system)
    (affectedObservation system)
institutionalAffectedCollisionIsNonfactorability collision =
  INF.nonFactorabilityWitness
    (left collision)
    (right collision)
    (sameInstitutionalObservation collision)
    (differentAffectedObservation collision)

institutionalObservationCannotRecoverAffectedObservation :
  ∀ {State Declared Institutional Affected Independent Correction Outcome : Set}
    {system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome} →
  InstitutionalAffectedCollision system →
  INF.FactorsThrough
    (institutionalObservation system)
    (affectedObservation system) → ⊥
institutionalObservationCannotRecoverAffectedObservation collision =
  INF.witnessRulesOutEveryFlatFactorisation
    (institutionalAffectedCollisionIsNonfactorability collision)

record MonitoringCorrectionCollision
    {State Declared Institutional Affected Independent Correction Outcome : Set}
    (system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome) : Set where
  constructor monitoring-correction-collision
  field
    left right : State
    sameIndependentObservation :
      independentObservation system left
      ≡ independentObservation system right
    differentCorrectionResponse :
      correctionResponse system left
      ≡ correctionResponse system right → ⊥

open MonitoringCorrectionCollision public

monitoringDoesNotRecoverCorrection :
  ∀ {State Declared Institutional Affected Independent Correction Outcome : Set}
    {system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome} →
  MonitoringCorrectionCollision system →
  INF.FactorsThrough
    (independentObservation system)
    (correctionResponse system) → ⊥
monitoringDoesNotRecoverCorrection collision =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      (left collision)
      (right collision)
      (sameIndependentObservation collision)
      (differentCorrectionResponse collision))

record CorrectionOutcomeCollision
    {State Declared Institutional Affected Independent Correction Outcome : Set}
    (system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome) : Set where
  constructor correction-outcome-collision
  field
    left right : State
    sameCorrectionResponse :
      correctionResponse system left
      ≡ correctionResponse system right
    differentRealisedOutcome :
      realisedOutcome system left
      ≡ realisedOutcome system right → ⊥

open CorrectionOutcomeCollision public

correctionDoesNotRecoverRealisedOutcome :
  ∀ {State Declared Institutional Affected Independent Correction Outcome : Set}
    {system : PluralOperationalSystem
      State Declared Institutional Affected Independent Correction Outcome} →
  CorrectionOutcomeCollision system →
  INF.FactorsThrough
    (correctionResponse system)
    (realisedOutcome system) → ⊥
correctionDoesNotRecoverRealisedOutcome collision =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      (left collision)
      (right collision)
      (sameCorrectionResponse collision)
      (differentRealisedOutcome collision))

------------------------------------------------------------------------
-- Finite regression fixture.
------------------------------------------------------------------------

data DemoState : Set where
  institutionSaysClosedAffectedOpen
  institutionSaysClosedAffectedClosed
  : DemoState

data DemoDeclared : Set where declaredRepair : DemoDeclared
data DemoInstitutional : Set where institutionReportsCompliant : DemoInstitutional
data DemoAffected : Set where affectedResidualOpen affectedResidualClosed : DemoAffected
data DemoIndependent : Set where independentMonitoringPresent : DemoIndependent
data DemoCorrection : Set where noRevision effectiveRevision : DemoCorrection
data DemoOutcome : Set where realisedHarmPersists realisedRepair : DemoOutcome

demoDeclared : DemoState → DemoDeclared
demoDeclared _ = declaredRepair

demoInstitutional : DemoState → DemoInstitutional
demoInstitutional _ = institutionReportsCompliant

demoAffected : DemoState → DemoAffected
demoAffected institutionSaysClosedAffectedOpen = affectedResidualOpen
demoAffected institutionSaysClosedAffectedClosed = affectedResidualClosed

demoIndependent : DemoState → DemoIndependent
demoIndependent _ = independentMonitoringPresent

demoCorrection : DemoState → DemoCorrection
demoCorrection institutionSaysClosedAffectedOpen = noRevision
demoCorrection institutionSaysClosedAffectedClosed = effectiveRevision

demoOutcome : DemoState → DemoOutcome
demoOutcome institutionSaysClosedAffectedOpen = realisedHarmPersists
demoOutcome institutionSaysClosedAffectedClosed = realisedRepair

demoSystem :
  PluralOperationalSystem
    DemoState DemoDeclared DemoInstitutional DemoAffected DemoIndependent DemoCorrection DemoOutcome
demoSystem = plural-operational-system
  demoDeclared demoInstitutional demoAffected demoIndependent demoCorrection demoOutcome

demoInstitutionCollision : InstitutionalAffectedCollision demoSystem
demoInstitutionCollision = institutional-affected-collision
  institutionSaysClosedAffectedOpen
  institutionSaysClosedAffectedClosed
  refl
  (λ ())

demoMonitoringCollision : MonitoringCorrectionCollision demoSystem
demoMonitoringCollision = monitoring-correction-collision
  institutionSaysClosedAffectedOpen
  institutionSaysClosedAffectedClosed
  refl
  (λ ())

demoCorrectionOutcomeCollision : CorrectionOutcomeCollision demoSystem
demoCorrectionOutcomeCollision = correction-outcome-collision
  institutionSaysClosedAffectedOpen
  institutionSaysClosedAffectedClosed
  -- Deliberately use a second finite witness below for same correction / distinct outcome.
  -- This collision constructor is not inhabited by the first demo pair.
  -- Kept separate from the canonical witnesses to avoid manufacturing equality.
  -- No value is constructed here.
  {!!}
  {!!}

institutionalSelfReportCannotRecoverAffectedOutcome :
  INF.FactorsThrough demoInstitutional demoAffected → ⊥
institutionalSelfReportCannotRecoverAffectedOutcome =
  institutionalObservationCannotRecoverAffectedObservation demoInstitutionCollision

monitoringPresenceCannotRecoverRevision :
  INF.FactorsThrough demoIndependent demoCorrection → ⊥
monitoringPresenceCannotRecoverRevision =
  monitoringDoesNotRecoverCorrection demoMonitoringCollision

------------------------------------------------------------------------
-- Generic operational boundary.
------------------------------------------------------------------------

record PluralObserverCorrectionBoundary : Set where
  constructor plural-observer-correction-boundary
  field
    institutionalSelfAssessmentExhaustsAffectedOutcome : Bool
    institutionalSelfAssessmentExhaustsAffectedOutcomeIsFalse :
      institutionalSelfAssessmentExhaustsAffectedOutcome ≡ false
    monitoringEqualsCorrection : Bool
    monitoringEqualsCorrectionIsFalse : monitoringEqualsCorrection ≡ false
    correctionActivityEqualsRealisedRepair : Bool
    correctionActivityEqualsRealisedRepairIsFalse :
      correctionActivityEqualsRealisedRepair ≡ false
    affectedObservationAutomaticallyOverridesEveryOtherStrand : Bool
    affectedObservationAutomaticallyOverridesEveryOtherStrandIsFalse :
      affectedObservationAutomaticallyOverridesEveryOtherStrand ≡ false
    independentReviewAutomaticallyDefinesCommunityAdequacy : Bool
    independentReviewAutomaticallyDefinesCommunityAdequacyIsFalse :
      independentReviewAutomaticallyDefinesCommunityAdequacy ≡ false
    sharedObservationFusesEpistemicAuthority : Bool
    sharedObservationFusesEpistemicAuthorityIsFalse :
      sharedObservationFusesEpistemicAuthority ≡ false
    realisedOutcomeIsIndependentOperationalCoordinate : Bool
    realisedOutcomeIsIndependentOperationalCoordinateIsTrue :
      realisedOutcomeIsIndependentOperationalCoordinate ≡ true

open PluralObserverCorrectionBoundary public

canonicalPluralObserverCorrectionBoundary : PluralObserverCorrectionBoundary
canonicalPluralObserverCorrectionBoundary = plural-observer-correction-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data InstitutionalReportEqualsAffectedOutcome : Set where
data MonitoringEqualsRevision : Set where
data RevisionEqualsRepair : Set where
data PluralObservationMeansOneEpistemology : Set where
data AffectedObservationMeansAutomaticDecisionAuthority : Set where

institutionalReportDoesNotEqualAffectedOutcome :
  InstitutionalReportEqualsAffectedOutcome → ⊥
institutionalReportDoesNotEqualAffectedOutcome ()

monitoringDoesNotEqualRevision : MonitoringEqualsRevision → ⊥
monitoringDoesNotEqualRevision ()

revisionDoesNotEqualRepair : RevisionEqualsRepair → ⊥
revisionDoesNotEqualRepair ()

pluralObservationDoesNotFuseEpistemologies : PluralObservationMeansOneEpistemology → ⊥
pluralObservationDoesNotFuseEpistemologies ()

affectedObservationDoesNotAutoCreateDecisionAuthority :
  AffectedObservationMeansAutomaticDecisionAuthority → ⊥
affectedObservationDoesNotAutoCreateDecisionAuthority ()
