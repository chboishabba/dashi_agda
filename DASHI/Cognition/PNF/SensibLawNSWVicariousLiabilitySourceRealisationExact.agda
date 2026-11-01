module DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilitySourceRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact as Act

------------------------------------------------------------------------
-- SOURCE-REALISED s 8 ROUTES
--
-- s 8 contains alternative route (a)/(b), so we preserve two rules rather than
-- flatten statutory OR into a conjunction. Both retain the s 8(2) exceptions.
------------------------------------------------------------------------

nswVicariousJurisdiction : Algebra.LegalProposition
nswVicariousJurisdiction = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:jurisdiction:NSW")
  Algebra.jurisdictionPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "jurisdiction:NSW")
  Negligence.auCommonLawSystem
  "the liability question is governed by the New South Wales Law Reform (Vicarious Liability) Act 1983"

actTemporalApplicability : Algebra.LegalProposition
actTemporalApplicability = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s3:temporal-applicability")
  Algebra.temporalPredicate
  (Ontology.stableId "tort:current")
  (Ontology.stableId "section:NSW-LRVLA:3")
  Negligence.auCommonLawSystem
  "the tort or wrongful act/omission is not outside the Act by reason of the pre-commencement boundary in s 3"

jurisdictionSource : SourceRule.PropositionSourceReceipt nswVicariousJurisdiction
jurisdictionSource = Act.reconstructionReceipt
  nswVicariousJurisdiction
  "Act as a whole; NSW enactment"
  "DASHI-NSW-LRVLA-jurisdiction"

temporalSource : SourceRule.PropositionSourceReceipt actTemporalApplicability
temporalSource = Act.sectionReceipt
  actTemporalApplicability
  "s 3"
  "NSW-LRVLA-s3-temporal"

s8RouteARole : SourceRole.SourceFormRoleReceipt
s8RouteARole = Act.reconstructionRole "DASHI-NSW-LRVLA-s8-route-a"

s8RouteBRole : SourceRole.SourceFormRoleReceipt
s8RouteBRole = Act.reconstructionRole "DASHI-NSW-LRVLA-s8-route-b"

s8RouteARealised : SourceRule.SourceRealisedLegalRule Act.s8RouteARule
s8RouteARealised = SourceRule.source-realised-legal-rule
  Act.actSource
  Act.actSourceRef refl
  "s 6; s 8(1)(a); s 8(2)"
  s8RouteARole refl refl refl
  (Source.citationCreatesAuthorityIsFalse Act.actSource)
  Act.s8FamilySource
  (Act.s6ServiceSource Algebra.∷ Act.s8TortSource Algebra.∷ Act.s8RouteASource Algebra.∷ Algebra.[])
  (Act.s8OwnAccountSource Algebra.∷ Act.s8PartnershipSource Algebra.∷ Algebra.[])
  Algebra.[]
  nswVicariousJurisdiction jurisdictionSource refl
  actTemporalApplicability temporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised s 8(1)(a) route; source-defined atoms plus DASHI conjunction, with s 8(2) negative branches preserved"

s8RouteBRealised : SourceRule.SourceRealisedLegalRule Act.s8RouteBRule
s8RouteBRealised = SourceRule.source-realised-legal-rule
  Act.actSource
  Act.actSourceRef refl
  "s 6; s 8(1)(b); s 8(2)"
  s8RouteBRole refl refl refl
  (Source.citationCreatesAuthorityIsFalse Act.actSource)
  Act.s8FamilySource
  (Act.s6ServiceSource Algebra.∷ Act.s8TortSource Algebra.∷ Act.s8RouteBSource Algebra.∷ Algebra.[])
  (Act.s8OwnAccountSource Algebra.∷ Act.s8PartnershipSource Algebra.∷ Algebra.[])
  Algebra.[]
  nswVicariousJurisdiction jurisdictionSource refl
  actTemporalApplicability temporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised s 8(1)(b) route; source-defined atoms plus DASHI conjunction, with s 8(2) negative branches preserved"

------------------------------------------------------------------------
-- Route identity remains a live coordinate even when the family is known.
------------------------------------------------------------------------

data S8Route : Set where
  routeA : S8Route
  routeB : S8Route

data CullenS8SubrouteFrontier : Set where
  subrouteUnresolved : CullenS8SubrouteFrontier
  subrouteSourcePaid : S8Route → CullenS8SubrouteFrontier

currentCullenS8SubrouteFrontier : CullenS8SubrouteFrontier
currentCullenS8SubrouteFrontier = subrouteUnresolved

data VicariousFamilyDeterminesS8Subroute : Set where
data S8RouteChoiceProvesUnderlyingTort : Set where

familyDoesNotDetermineSubroute : VicariousFamilyDeterminesS8Subroute → ⊥
familyDoesNotDetermineSubroute ()

routeChoiceDoesNotProveTort : S8RouteChoiceProvesUnderlyingTort → ⊥
routeChoiceDoesNotProveTort ()
