module DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

------------------------------------------------------------------------
-- LAW REFORM (VICARIOUS LIABILITY) ACT 1983 (NSW)
--
-- Official current source:
--   https://legislation.nsw.gov.au/view/whole/html/inforce/current/act-1983-038
--
-- Atomic reading:
--   s 6  : police officer -> person in service of Crown
--   s 8  : source-defined Crown vicarious-liability routes
--   s 9B : procedural routing of police tort claims
--   s 9C : initial court determination when Crown/officer both parties
--   s 9E : Part 4 does not itself create Crown vicarious liability
--
-- No section heading or procedural routing proposition is allowed to silently
-- establish that an underlying tort exists.
------------------------------------------------------------------------

actSource : Source.AttributedSource
actSource = Source.mkNoDOISource
  "Parliament of New South Wales; NSW Parliamentary Counsel"
  "Law Reform (Vicarious Liability) Act 1983 No 38"
  "NSW legislation website — current consolidated Act"
  "1983"
  "https://legislation.nsw.gov.au/view/whole/html/inforce/current/act-1983-038"
  Source.governmentSource
  "primary statutory text; section-level propositions preserve exact lineage and do not by citation establish tort, vicarious liability, court competence or remedy"
  Source.publicAttribution

actLegalSource : Ontology.LegalSource
actLegalSource = Ontology.legalSource
  (Ontology.stableId "source:NSW:Law-Reform-Vicarious-Liability-Act-1983-No38")
  Negligence.auCommonLawSystem
  Ontology.statute
  "Law Reform (Vicarious Liability) Act 1983 No 38 (NSW)"
  "current version; point-in-time applicability separately required"
  "New South Wales"

actSourceRef : Algebra.LegalSourceRef
actSourceRef = Algebra.legal-source-ref
  actLegalSource
  "Parliament of New South Wales"
  "Law Reform (Vicarious Liability) Act 1983 No 38"
  "NSW Act No 38 of 1983"

actAuthority : Edge.SourceIdentity
actAuthority = Edge.source-identity
  "Parliament of New South Wales"
  "Law Reform (Vicarious Liability) Act 1983 No 38"
  "NSW Act No 38 of 1983"
  Edge.legislation

legislativeRole : String → SourceRole.SourceFormRoleReceipt
legislativeRole ref = SourceRole.source-form-role-receipt
  actAuthority Ontology.statute Algebra.legislativeRuleRole ref true true

reconstructionRole : String → SourceRole.SourceFormRoleReceipt
reconstructionRole ref = SourceRole.source-form-role-receipt
  actAuthority Ontology.statute Algebra.dashReconstructionRole ref true true

sectionReceipt :
  (p : Algebra.LegalProposition) →
  String → String →
  SourceRule.PropositionSourceReceipt p
sectionReceipt p locator reference = SourceRule.proposition-source-receipt
  actSource actSourceRef locator SourceRule.primarySourceLayer
  (legislativeRole reference)
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse actSource)
  reference

reconstructionReceipt :
  (p : Algebra.LegalProposition) →
  String → String →
  SourceRule.PropositionSourceReceipt p
reconstructionReceipt p locator reference = SourceRule.proposition-source-receipt
  actSource actSourceRef locator SourceRule.repositoryReconstructionLayer
  (reconstructionRole reference)
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse actSource)
  reference

------------------------------------------------------------------------
-- Section 6 — police officer status.
------------------------------------------------------------------------

policeOfficer : Algebra.LegalProposition
policeOfficer = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s6:police-officer")
  Algebra.factualFeature
  (Ontology.stableId "actor:police-officer")
  (Ontology.stableId "section:NSW-LRVLA:6")
  Negligence.auCommonLawSystem
  "the relevant person was a police officer for purposes of the Act"

personInServiceOfCrown : Algebra.LegalProposition
personInServiceOfCrown = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s6:person-in-service-of-Crown")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:police-officer")
  (Ontology.stableId "party:Crown-NSW")
  Negligence.auCommonLawSystem
  "for purposes of the Act, the police officer is deemed a person in the service of the Crown"

s6Rule : Algebra.LegalRule
s6Rule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-LRVLA:s6:police-in-service-of-Crown")
  (policeOfficer ∷ []) personInServiceOfCrown [] []
  actSourceRef Algebra.legislativeRuleRole
  "s 6 current source text" "New South Wales"

------------------------------------------------------------------------
-- Section 8 — true source-defined Crown vicarious liability.
------------------------------------------------------------------------

tortCommittedByPersonInService : Algebra.LegalProposition
tortCommittedByPersonInService = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8:tort-by-person-in-service")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:person-in-service-of-Crown")
  (Ontology.stableId "wrong:tort:current")
  Negligence.auCommonLawSystem
  "a tort was committed by a person in the service of the Crown"

functionInCourseOrIncidentOfService : Algebra.LegalProposition
functionInCourseOrIncidentOfService = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8-1-a:course-or-incident")
  Algebra.relationalFeature
  (Ontology.stableId "function:current")
  (Ontology.stableId "service:Crown")
  Negligence.auCommonLawSystem
  "performance or purported performance of the function was in the course of or incident to service with the Crown"

functionDirectedOrIncidentalToCrownActivity : Algebra.LegalProposition
functionDirectedOrIncidentalToCrownActivity = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8-1-b:directed-or-incidental")
  Algebra.relationalFeature
  (Ontology.stableId "function:current")
  (Ontology.stableId "activity:Crown")
  Negligence.auCommonLawSystem
  "performance or purported performance of the function was directed to or incidental to an activity of the Crown"

ownAccountBusinessException : Algebra.LegalProposition
ownAccountBusinessException = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8-2-a:own-account-exception")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:person-in-service-of-Crown")
  (Ontology.stableId "section:NSW-LRVLA:8-2-a")
  Negligence.auCommonLawSystem
  "the tort was committed in a business, enterprise, undertaking or activity carried on by the person on the person's own account"

partnershipAccountException : Algebra.LegalProposition
partnershipAccountException = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8-2-b:partnership-exception")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:person-in-service-of-Crown")
  (Ontology.stableId "section:NSW-LRVLA:8-2-b")
  Negligence.auCommonLawSystem
  "the tort was committed in an activity carried on by a partnership of which the person was a member on account of the partnership"

crownVicariousLiabilityRecognised : Algebra.LegalProposition
crownVicariousLiabilityRecognised = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s8:Crown-vicarious-liability")
  Algebra.doctrinalPredicate
  (Ontology.stableId "party:Crown-NSW")
  (Ontology.stableId "liability-family:vicarious")
  Negligence.auCommonLawSystem
  "the source-defined s 8 route recognises Crown vicarious liability for the established tort"

s8RouteARule : Algebra.LegalRule
s8RouteARule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-LRVLA:s8:route-a")
  (personInServiceOfCrown ∷ tortCommittedByPersonInService ∷ functionInCourseOrIncidentOfService ∷ [])
  crownVicariousLiabilityRecognised
  (ownAccountBusinessException ∷ partnershipAccountException ∷ []) []
  actSourceRef Algebra.dashReconstructionRole
  "DASHI conjunction preserving s 8(1)(a) and s 8(2) structure"
  "New South Wales"

s8RouteBRule : Algebra.LegalRule
s8RouteBRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-LRVLA:s8:route-b")
  (personInServiceOfCrown ∷ tortCommittedByPersonInService ∷ functionDirectedOrIncidentalToCrownActivity ∷ [])
  crownVicariousLiabilityRecognised
  (ownAccountBusinessException ∷ partnershipAccountException ∷ []) []
  actSourceRef Algebra.dashReconstructionRole
  "DASHI conjunction preserving s 8(1)(b) and s 8(2) structure"
  "New South Wales"

------------------------------------------------------------------------
-- Part 4 police-claim routing and anti-promotion clause.
------------------------------------------------------------------------

policeTortClaim : Algebra.LegalProposition
policeTortClaim = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s9B:police-tort-claim")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-LRVLA:9B")
  Negligence.auCommonLawSystem
  "the damages claim is for a tort allegedly committed by a police officer in performance or purported performance of police functions"

claimMayInsteadBeMadeAgainstCrown : Algebra.LegalProposition
claimMayInsteadBeMadeAgainstCrown = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s9B-2:claim-against-Crown")
  Algebra.jurisdictionPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "party:Crown-NSW")
  Negligence.auCommonLawSystem
  "subject to Part 4, the police tort claim may instead be made against the Crown"

part4DoesNotCreateVicariousLiability : Algebra.LegalProposition
part4DoesNotCreateVicariousLiability = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-LRVLA:s9E-a:Part4-no-creation")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-LRVLA:9E-a")
  Negligence.auCommonLawSystem
  "Part 4 does not make the Crown vicariously liable if the Crown would not otherwise be vicariously liable for the tort"

------------------------------------------------------------------------
-- Typed source receipts for direct and reconstructed propositions.
------------------------------------------------------------------------

s6PoliceSource : SourceRule.PropositionSourceReceipt policeOfficer
s6PoliceSource = sectionReceipt policeOfficer "s 6" "NSW-LRVLA-s6-police"

s6ServiceSource : SourceRule.PropositionSourceReceipt personInServiceOfCrown
s6ServiceSource = sectionReceipt personInServiceOfCrown "s 6" "NSW-LRVLA-s6-service"

s8TortSource : SourceRule.PropositionSourceReceipt tortCommittedByPersonInService
s8TortSource = sectionReceipt tortCommittedByPersonInService "s 8(1)" "NSW-LRVLA-s8-tort"

s8RouteASource : SourceRule.PropositionSourceReceipt functionInCourseOrIncidentOfService
s8RouteASource = sectionReceipt functionInCourseOrIncidentOfService "s 8(1)(a)" "NSW-LRVLA-s8-1-a"

s8RouteBSource : SourceRule.PropositionSourceReceipt functionDirectedOrIncidentalToCrownActivity
s8RouteBSource = sectionReceipt functionDirectedOrIncidentalToCrownActivity "s 8(1)(b)" "NSW-LRVLA-s8-1-b"

s8OwnAccountSource : SourceRule.PropositionSourceReceipt ownAccountBusinessException
s8OwnAccountSource = sectionReceipt ownAccountBusinessException "s 8(2)(a)" "NSW-LRVLA-s8-2-a"

s8PartnershipSource : SourceRule.PropositionSourceReceipt partnershipAccountException
s8PartnershipSource = sectionReceipt partnershipAccountException "s 8(2)(b)" "NSW-LRVLA-s8-2-b"

s8FamilySource : SourceRule.PropositionSourceReceipt crownVicariousLiabilityRecognised
s8FamilySource = reconstructionReceipt crownVicariousLiabilityRecognised "s 8" "DASHI-s8-family-recognition"

s9BClaimSource : SourceRule.PropositionSourceReceipt policeTortClaim
s9BClaimSource = sectionReceipt policeTortClaim "s 9B(1)" "NSW-LRVLA-s9B-1"

s9BRouteSource : SourceRule.PropositionSourceReceipt claimMayInsteadBeMadeAgainstCrown
s9BRouteSource = sectionReceipt claimMayInsteadBeMadeAgainstCrown "s 9B(2)" "NSW-LRVLA-s9B-2"

s9ENoCreationSource : SourceRule.PropositionSourceReceipt part4DoesNotCreateVicariousLiability
s9ENoCreationSource = sectionReceipt part4DoesNotCreateVicariousLiability "s 9E(a)" "NSW-LRVLA-s9E-a"

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data PoliceOfficerAutomaticallyCommitsTort : Set where
data PoliceTortClaimAutomaticallyCreatesCrownLiability : Set where
data S9BProceduralRoutingIsFamilyRecognition : Set where
data S9EAntiCreationMeansNoVicariousLiability : Set where
data VicariousFamilyMeansUnderlyingTortProved : Set where

policeStatusDoesNotCreateTort : PoliceOfficerAutomaticallyCommitsTort → ⊥
policeStatusDoesNotCreateTort ()

policeClaimDoesNotCreateCrownLiability : PoliceTortClaimAutomaticallyCreatesCrownLiability → ⊥
policeClaimDoesNotCreateCrownLiability ()

s9BDoesNotRecogniseFamilyByItself : S9BProceduralRoutingIsFamilyRecognition → ⊥
s9BDoesNotRecogniseFamilyByItself ()

s9EAntiCreationDoesNotNegateVicariousLiability : S9EAntiCreationMeansNoVicariousLiability → ⊥
s9EAntiCreationDoesNotNegateVicariousLiability ()

familyRecognitionDoesNotProveUnderlyingTort : VicariousFamilyMeansUnderlyingTortProved → ⊥
familyRecognitionDoesNotProveUnderlyingTort ()
