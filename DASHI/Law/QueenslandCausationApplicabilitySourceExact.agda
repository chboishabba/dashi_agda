module DASHI.Law.QueenslandCausationApplicabilitySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Law.QueenslandButForSourceBoundaryExact as Source

------------------------------------------------------------------------
-- QUEENSLAND CIVIL LIABILITY ACT 2003 -- APPLICATION / CAUSATION BOUNDARY
--
-- Primary-source coordinates from the current Queensland legislation.
-- This module deliberately records applicability and non-codification limits
-- alongside ss 10-12 so a parser or WrongType declaration cannot silently
-- universalise the statutory causation rule.
------------------------------------------------------------------------

record QueenslandCLAApplicabilityCoordinates : Set where
  constructor queenslandCLAApplicabilityCoordinates
  field
    appliesToCivilClaimForDamagesForHarmSubjectToExclusions : Bool
    appliesToCivilClaimForDamagesForHarmSubjectToExclusionsIsTrue :
      appliesToCivilClaimForDamagesForHarmSubjectToExclusions ≡ true

    actCreatesCauseOfAction : Bool
    actCreatesCauseOfActionIsFalse : actCreatesCauseOfAction ≡ false

    actIsCompleteCodificationOfCivilClaimsLaw : Bool
    actIsCompleteCodificationOfCivilClaimsLawIsFalse :
      actIsCompleteCodificationOfCivilClaimsLaw ≡ false

    section11SeparatesFactualAndScopeElements : Bool
    section11SeparatesFactualAndScopeElementsIsTrue :
      section11SeparatesFactualAndScopeElements ≡ true

    primarySource : Source.LegalSourceAttribution
    applicationReference : String
    nonCodificationReference : String
    causationReference : String

open QueenslandCLAApplicabilityCoordinates public

canonicalQueenslandCLAApplicability : QueenslandCLAApplicabilityCoordinates
canonicalQueenslandCLAApplicability =
  queenslandCLAApplicabilityCoordinates
    true refl
    false refl
    false refl
    true refl
    Source.queenslandCivilLiabilityAct
    "Civil Liability Act 2003 (Qld) s 4, subject to s 5 exclusions"
    "Civil Liability Act 2003 (Qld) s 7(1), s 7(5)"
    "Civil Liability Act 2003 (Qld) ss 10-12"

------------------------------------------------------------------------
-- A source-backed causation declaration needs an applicability receipt for the
-- legal matter; source authority alone does not prove that the Act governs it.
------------------------------------------------------------------------

record QueenslandCausationApplicabilityReceipt : Set where
  constructor queenslandCausationApplicabilityReceipt
  field
    civilClaimForDamagesForHarmReceipt : Set
    section5ExclusionResolvedReceipt : Set
    temporalApplicationReceipt : Set
    legalSystemAndJurisdictionReceipt : Set
    sourceValidityReceipt : Set
    applicabilityResolverReference : String

open QueenslandCausationApplicabilityReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data QueenslandCLAAlwaysAppliesToEveryWrongType : Set where
data Section11CreatesIndependentCauseOfAction : Set where
data Section11CodifiesAllCausationLaw : Set where
data SourceAuthorityAutomaticallyEstablishesApplicability : Set where

authoritativeActDoesNotApplyToEveryWrongType :
  QueenslandCLAAlwaysAppliesToEveryWrongType → ⊥
authoritativeActDoesNotApplyToEveryWrongType ()

section11DoesNotCreateIndependentCauseOfAction :
  Section11CreatesIndependentCauseOfAction → ⊥
section11DoesNotCreateIndependentCauseOfAction ()

section11DoesNotClaimCompleteCausationCodification :
  Section11CodifiesAllCausationLaw → ⊥
section11DoesNotClaimCompleteCausationCodification ()

sourceAuthorityDoesNotAutoEstablishApplicability :
  SourceAuthorityAutomaticallyEstablishesApplicability → ⊥
sourceAuthorityDoesNotAutoEstablishApplicability ()

record QueenslandCausationApplicabilityBoundary : Set where
  constructor queenslandCausationApplicabilityBoundary
  field
    primarySourceAndApplicabilityAreSeparate : Bool
    primarySourceAndApplicabilityAreSeparateIsTrue :
      primarySourceAndApplicabilityAreSeparate ≡ true
    section11IsElementRuleNotStandaloneCause : Bool
    section11IsElementRuleNotStandaloneCauseIsTrue :
      section11IsElementRuleNotStandaloneCause ≡ true
    nonCodificationPreserved : Bool
    nonCodificationPreservedIsTrue : nonCodificationPreserved ≡ true

canonicalQueenslandCausationApplicabilityBoundary :
  QueenslandCausationApplicabilityBoundary
canonicalQueenslandCausationApplicabilityBoundary =
  queenslandCausationApplicabilityBoundary true refl true refl true refl
