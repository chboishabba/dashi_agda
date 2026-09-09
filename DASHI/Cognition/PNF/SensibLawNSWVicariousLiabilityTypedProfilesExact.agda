module DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityTypedProfilesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawSourceConditionedTypedLiabilityExact as Typed
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact as Act
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilitySourceRealisationExact as Realised

------------------------------------------------------------------------
-- SOURCE-CONDITIONED TYPED PROFILES FOR THE TWO s 8 ROUTES.
--
-- These are jurisdictional/statutory schemas. They do not assert that either
-- route is established on Cullen facts, nor that the underlying tort exists.
------------------------------------------------------------------------

familyAttachment : Downstream.PrimarySourceAttachment Downstream.liabilityClassificationStage
familyAttachment = Downstream.primary-source-attachment
  Act.actSource "s 8" Act.crownVicariousLiabilityRecognised
  "Law Reform (Vicarious Liability) Act 1983 (NSW) s 8 is the substantive source family; the proposition is a DASHI reconstruction of the source-defined conjunctive route."
  (Source.citationCreatesAuthorityIsFalse Act.actSource)

conditionAttachment :
  Algebra.LegalProposition → String →
  Downstream.PrimarySourceAttachment Downstream.liabilityConditionStage
conditionAttachment p locator = Downstream.primary-source-attachment
  Act.actSource locator p
  "source-defined positive condition for the selected s 8 vicarious-liability route"
  (Source.citationCreatesAuthorityIsFalse Act.actSource)

limitationAttachment :
  Algebra.LegalProposition → String →
  Downstream.PrimarySourceAttachment Downstream.limitationOrDefeaterStage
limitationAttachment p locator = Downstream.primary-source-attachment
  Act.actSource locator p
  "source-defined s 8(2) limitation/exception; case application must fail this exact atom before the route can compile"
  (Source.citationCreatesAuthorityIsFalse Act.actSource)

routeAProfile : Downstream.TypedLiabilityProfile Negligence.negligenceWrongType
routeAProfile = Downstream.typed-liability-profile
  Downstream.vicariousLiability
  (familyAttachment ∷ [])
  (Act.personInServiceOfCrown ∷ Act.tortCommittedByPersonInService ∷ Act.functionInCourseOrIncidentOfService ∷ [])
  (conditionAttachment Act.personInServiceOfCrown "s 6" ∷
   conditionAttachment Act.tortCommittedByPersonInService "s 8(1)" ∷
   conditionAttachment Act.functionInCourseOrIncidentOfService "s 8(1)(a)" ∷ [])
  (Act.ownAccountBusinessException ∷ Act.partnershipAccountException ∷ [])
  (limitationAttachment Act.ownAccountBusinessException "s 8(2)(a)" ∷
   limitationAttachment Act.partnershipAccountException "s 8(2)(b)" ∷ [])
  Status.courtJurisdiction
  Negligence.auCommonLawSystem refl
  "NSW Law Reform (Vicarious Liability) Act 1983 s 8(1)(a) source-conditioned typed profile"

routeBProfile : Downstream.TypedLiabilityProfile Negligence.negligenceWrongType
routeBProfile = Downstream.typed-liability-profile
  Downstream.vicariousLiability
  (familyAttachment ∷ [])
  (Act.personInServiceOfCrown ∷ Act.tortCommittedByPersonInService ∷ Act.functionDirectedOrIncidentalToCrownActivity ∷ [])
  (conditionAttachment Act.personInServiceOfCrown "s 6" ∷
   conditionAttachment Act.tortCommittedByPersonInService "s 8(1)" ∷
   conditionAttachment Act.functionDirectedOrIncidentalToCrownActivity "s 8(1)(b)" ∷ [])
  (Act.ownAccountBusinessException ∷ Act.partnershipAccountException ∷ [])
  (limitationAttachment Act.ownAccountBusinessException "s 8(2)(a)" ∷
   limitationAttachment Act.partnershipAccountException "s 8(2)(b)" ∷ [])
  Status.courtJurisdiction
  Negligence.auCommonLawSystem refl
  "NSW Law Reform (Vicarious Liability) Act 1983 s 8(1)(b) source-conditioned typed profile"

------------------------------------------------------------------------
-- Membership-indexed source functions.  Pattern matching keeps source identity
-- aligned with the exact condition/limitation position rather than using a
-- parallel list index.
------------------------------------------------------------------------

routeAConditionSource :
  ∀ {p} → p Algebra.∈ Downstream.conditions routeAProfile →
  DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact.PropositionSourceReceipt p
routeAConditionSource Algebra.here = Act.s6ServiceSource
routeAConditionSource (Algebra.there Algebra.here) = Act.s8TortSource
routeAConditionSource (Algebra.there (Algebra.there Algebra.here)) = Act.s8RouteASource

routeBConditionSource :
  ∀ {p} → p Algebra.∈ Downstream.conditions routeBProfile →
  DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact.PropositionSourceReceipt p
routeBConditionSource Algebra.here = Act.s6ServiceSource
routeBConditionSource (Algebra.there Algebra.here) = Act.s8TortSource
routeBConditionSource (Algebra.there (Algebra.there Algebra.here)) = Act.s8RouteBSource

routeALimitationSource :
  ∀ {p} → p Algebra.∈ Downstream.limitationsAndDefeaters routeAProfile →
  DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact.PropositionSourceReceipt p
routeALimitationSource Algebra.here = Act.s8OwnAccountSource
routeALimitationSource (Algebra.there Algebra.here) = Act.s8PartnershipSource

routeBLimitationSource :
  ∀ {p} → p Algebra.∈ Downstream.limitationsAndDefeaters routeBProfile →
  DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact.PropositionSourceReceipt p
routeBLimitationSource Algebra.here = Act.s8OwnAccountSource
routeBLimitationSource (Algebra.there Algebra.here) = Act.s8PartnershipSource

routeASourceConditionedProfile : Typed.SourceConditionedTypedLiabilityProfile routeAProfile
routeASourceConditionedProfile = Typed.source-conditioned-typed-liability-profile
  Act.crownVicariousLiabilityRecognised
  Act.s8FamilySource refl refl
  Act.s8RouteARule Realised.s8RouteARealised refl
  routeAConditionSource
  routeALimitationSource
  Realised.actTemporalApplicability Realised.temporalSource refl
  Realised.nswVicariousJurisdiction Realised.jurisdictionSource refl
  refl
  "source-conditioned typed vicarious-liability profile for statutory route s 8(1)(a)"

routeBSourceConditionedProfile : Typed.SourceConditionedTypedLiabilityProfile routeBProfile
routeBSourceConditionedProfile = Typed.source-conditioned-typed-liability-profile
  Act.crownVicariousLiabilityRecognised
  Act.s8FamilySource refl refl
  Act.s8RouteBRule Realised.s8RouteBRealised refl
  routeBConditionSource
  routeBLimitationSource
  Realised.actTemporalApplicability Realised.temporalSource refl
  Realised.nswVicariousJurisdiction Realised.jurisdictionSource refl
  refl
  "source-conditioned typed vicarious-liability profile for statutory route s 8(1)(b)"

------------------------------------------------------------------------
-- Boundary: knowing the source-conditioned family does not resolve the OR.
------------------------------------------------------------------------

data EitherProfileMeansBothRoutesApply : Set where
data SourceConditionedProfileProvesUnderlyingTort : Set where

eitherProfileDoesNotCollapseRoutes : EitherProfileMeansBothRoutesApply → ⊥
eitherProfileDoesNotCollapseRoutes ()

profileDoesNotProveTort : SourceConditionedProfileProvesUnderlyingTort → ⊥
profileDoesNotProveTort ()
