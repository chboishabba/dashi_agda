module DASHI.Cognition.PNF.SensibLawConsumerQueryLeastPrivilegeRegressionExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand

------------------------------------------------------------------------
-- EXACT LEAST-PRIVILEGE REGRESSIONS
------------------------------------------------------------------------

legalWhoSaidWhatDoesNotRequireApplicability :
  Demand.Requires Consumer.legalConsumer Demand.whoSaidWhatQuery Demand.applicabilityCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireApplicability ()

legalWhoSaidWhatDoesNotRequireLegalSourceAuthority :
  Demand.Requires Consumer.legalConsumer Demand.whoSaidWhatQuery Demand.legalSourceAuthorityCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireLegalSourceAuthority ()

legalWhoSaidWhatDoesNotRequireSemanticAdmissionAuthority :
  Demand.Requires Consumer.legalConsumer Demand.whoSaidWhatQuery Demand.semanticAdmissionAuthorityCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireSemanticAdmissionAuthority ()

legalWhoSaidWhatDoesNotRequireJurisdiction :
  Demand.Requires Consumer.legalConsumer Demand.whoSaidWhatQuery Demand.jurisdictionCoordinate → ⊥
legalWhoSaidWhatDoesNotRequireJurisdiction ()

legalDiscourseRoleDoesNotRequireApplicability :
  Demand.Requires Consumer.legalConsumer Demand.legalDiscourseRoleQuery Demand.applicabilityCoordinate → ⊥
legalDiscourseRoleDoesNotRequireApplicability ()

legalDiscourseRoleDoesNotRequireLiability :
  Demand.Requires Consumer.legalConsumer Demand.legalDiscourseRoleQuery Demand.liabilityCoordinate → ⊥
legalDiscourseRoleDoesNotRequireLiability ()

generalWhoSaidWhatDoesNotRequireLegalRole :
  Demand.Requires Consumer.generalSemanticConsumer Demand.whoSaidWhatQuery Demand.legalRoleCoordinate → ⊥
generalWhoSaidWhatDoesNotRequireLegalRole ()

------------------------------------------------------------------------
-- Conversely, the strong legal query owns proof-bearing requirements.
------------------------------------------------------------------------

legalApplicabilityReallyRequiresOccurrence :
  Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.occurrenceCoordinate
legalApplicabilityReallyRequiresOccurrence = Demand.legalApplicabilityNeedsOccurrence

legalApplicabilityReallyRequiresLegalSourceAuthority :
  Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.legalSourceAuthorityCoordinate
legalApplicabilityReallyRequiresLegalSourceAuthority = Demand.legalApplicabilityNeedsLegalSourceAuthority

legalApplicabilityDoesNotRequireSemanticAdmissionAuthority :
  Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.semanticAdmissionAuthorityCoordinate → ⊥
legalApplicabilityDoesNotRequireSemanticAdmissionAuthority ()

legalApplicabilityReallyRequiresJurisdiction :
  Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.jurisdictionCoordinate
legalApplicabilityReallyRequiresJurisdiction = Demand.legalApplicabilityNeedsJurisdiction

------------------------------------------------------------------------
-- Query broadening is obligation growth, not parse mutation.
------------------------------------------------------------------------

data CheapQuerySecretlyContainsFullLegalStack : Set where
data StrongQueryCanBorrowMissingLegalSourceAuthorityFromAttribution : Set where
data QueryBroadeningReparsesText : Set where

cheapQueryDoesNotSecretlyContainFullLegalStack : CheapQuerySecretlyContainsFullLegalStack → ⊥
cheapQueryDoesNotSecretlyContainFullLegalStack ()

strongQueryCannotBorrowMissingLegalSourceAuthorityFromAttribution :
  StrongQueryCanBorrowMissingLegalSourceAuthorityFromAttribution → ⊥
strongQueryCannotBorrowMissingLegalSourceAuthorityFromAttribution ()

queryBroadeningDoesNotReparseText : QueryBroadeningReparsesText → ⊥
queryBroadeningDoesNotReparseText ()
