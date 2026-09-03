module DASHI.Cognition.PNF.SensibLawConsumerQueryLeastPrivilegeRegressionExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand

------------------------------------------------------------------------
-- EXACT LEAST-PRIVILEGE REGRESSIONS
--
-- These are indexed impossibilities over the actual `Requires` relation, not
-- policy comments.  A consumer may be legal while asking a cheap general
-- discourse question; absent constructors are therefore meaningful here.
------------------------------------------------------------------------

legalWhoSaidWhatDoesNotRequireApplicability :
  Demand.Requires
    Consumer.legalConsumer
    Demand.whoSaidWhatQuery
    Demand.applicabilityCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireApplicability ()

legalWhoSaidWhatDoesNotRequireAuthority :
  Demand.Requires
    Consumer.legalConsumer
    Demand.whoSaidWhatQuery
    Demand.authorityCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireAuthority ()

legalWhoSaidWhatDoesNotRequireJurisdiction :
  Demand.Requires
    Consumer.legalConsumer
    Demand.whoSaidWhatQuery
    Demand.jurisdictionCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireJurisdiction ()

legalDiscourseRoleDoesNotRequireApplicability :
  Demand.Requires
    Consumer.legalConsumer
    Demand.legalDiscourseRoleQuery
    Demand.applicabilityCoordinate → ⊥
legalDiscourseRoleDoesNotRequireApplicability ()

legalDiscourseRoleDoesNotRequireLiability :
  Demand.Requires
    Consumer.legalConsumer
    Demand.legalDiscourseRoleQuery
    Demand.liabilityCoordinate → ⊥
legalDiscourseRoleDoesNotRequireLiability ()

generalWhoSaidWhatDoesNotRequireLegalRole :
  Demand.Requires
    Consumer.generalSemanticConsumer
    Demand.whoSaidWhatQuery
    Demand.legalRoleCoordinate → ⊥
generalWhoSaidWhatDoesNotRequireLegalRole ()

------------------------------------------------------------------------
-- Conversely, the strong legal query owns proof-bearing requirements.
------------------------------------------------------------------------

legalApplicabilityReallyRequiresOccurrence :
  Demand.Requires
    Consumer.legalConsumer
    Demand.legalApplicabilityQuery
    Demand.occurrenceCoordinate
legalApplicabilityReallyRequiresOccurrence = Demand.legalApplicabilityNeedsOccurrence

legalApplicabilityReallyRequiresAuthority :
  Demand.Requires
    Consumer.legalConsumer
    Demand.legalApplicabilityQuery
    Demand.authorityCoordinate
legalApplicabilityReallyRequiresAuthority = Demand.legalApplicabilityNeedsAuthority

legalApplicabilityReallyRequiresJurisdiction :
  Demand.Requires
    Consumer.legalConsumer
    Demand.legalApplicabilityQuery
    Demand.jurisdictionCoordinate
legalApplicabilityReallyRequiresJurisdiction = Demand.legalApplicabilityNeedsJurisdiction

------------------------------------------------------------------------
-- Query broadening is obligation growth, not parse mutation.
------------------------------------------------------------------------

data CheapQuerySecretlyContainsFullLegalStack : Set where
data StrongQueryCanBorrowMissingAuthorityFromAttribution : Set where

data QueryBroadeningReparsesText : Set where

cheapQueryDoesNotSecretlyContainFullLegalStack :
  CheapQuerySecretlyContainsFullLegalStack → ⊥
cheapQueryDoesNotSecretlyContainFullLegalStack ()

strongQueryCannotBorrowMissingAuthorityFromAttribution :
  StrongQueryCanBorrowMissingAuthorityFromAttribution → ⊥
strongQueryCannotBorrowMissingAuthorityFromAttribution ()

queryBroadeningDoesNotReparseText : QueryBroadeningReparsesText → ⊥
queryBroadeningDoesNotReparseText ()
