module DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact where

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

nswCivilLiabilityActSource : Source.AttributedSource
nswCivilLiabilityActSource = Source.mkNoDOISource
  "Parliament of New South Wales; NSW Parliamentary Counsel"
  "Civil Liability Act 2002 No 22"
  "NSW legislation website — current consolidated Act"
  "2002"
  "https://legislation.nsw.gov.au/view/html/inforce/current/act-2002-022"
  Source.governmentSource
  "primary statutory text; section-level formalisation preserves statutory propositions versus DASHI reconstructed implications"
  Source.publicAttribution

nswCivilLiabilityActLegalSource : Ontology.LegalSource
nswCivilLiabilityActLegalSource = Ontology.legalSource
  (Ontology.stableId "source:NSW:Civil-Liability-Act-2002-No22")
  Negligence.auCommonLawSystem Ontology.statute
  "Civil Liability Act 2002 No 22 (NSW)"
  "point-in-time applicability separately required" "New South Wales"

nswCivilLiabilityActSourceRef : Algebra.LegalSourceRef
nswCivilLiabilityActSourceRef = Algebra.legal-source-ref
  nswCivilLiabilityActLegalSource "Parliament of New South Wales"
  "Civil Liability Act 2002 No 22" "NSW Act No 22 of 2002"

nswCivilLiabilityActAuthority : Edge.SourceIdentity
nswCivilLiabilityActAuthority = Edge.source-identity
  "Parliament of New South Wales" "Civil Liability Act 2002 No 22"
  "NSW Act No 22 of 2002" Edge.legislation

legislativeRole : String → SourceRole.SourceFormRoleReceipt
legislativeRole ref = SourceRole.source-form-role-receipt
  nswCivilLiabilityActAuthority Ontology.statute Algebra.legislativeRuleRole ref true true

reconstructionRole : String → SourceRole.SourceFormRoleReceipt
reconstructionRole ref = SourceRole.source-form-role-receipt
  nswCivilLiabilityActAuthority Ontology.statute Algebra.dashReconstructionRole ref true true

sectionReceipt :
  (p : Algebra.LegalProposition) →
  Negligence.auCommonLawSystem ≡ Algebra.legalSystem p →
  String → String → SourceRule.PropositionSourceReceipt p
sectionReceipt p system locator reference = SourceRule.proposition-source-receipt
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef locator
  SourceRule.primarySourceLayer (legislativeRole reference) system refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource) reference

reconstructionReceipt :
  (p : Algebra.LegalProposition) →
  Negligence.auCommonLawSystem ≡ Algebra.legalSystem p →
  String → String → SourceRule.PropositionSourceReceipt p
reconstructionReceipt p system locator reference = SourceRule.proposition-source-receipt
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef locator
  SourceRule.repositoryReconstructionLayer (reconstructionRole reference) system refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource) reference

nswJurisdictionPredicate : Algebra.LegalProposition
nswJurisdictionPredicate = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:jurisdiction:NSW") Algebra.jurisdictionPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "jurisdiction:NSW")
  Negligence.auCommonLawSystem
  "the claim falls within the NSW legal-system scope relevant to the Civil Liability Act"

nswCurrentTemporalPredicate : Algebra.LegalProposition
nswCurrentTemporalPredicate = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:temporal:applicable-version") Algebra.temporalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "source-version:NSW-CLA:applicable")
  Negligence.auCommonLawSystem
  "the event/claim is governed by the applicable point-in-time version of the statutory provision"

nswJurisdictionSource : SourceRule.PropositionSourceReceipt nswJurisdictionPredicate
nswJurisdictionSource = reconstructionReceipt nswJurisdictionPredicate refl
  "Civil Liability Act 2002 (NSW), Act-level NSW scope"
  "typed NSW system-scope reconstruction; court/personal jurisdiction remains separate"

nswCurrentTemporalSource : SourceRule.PropositionSourceReceipt nswCurrentTemporalPredicate
nswCurrentTemporalSource = reconstructionReceipt nswCurrentTemporalPredicate refl
  "Civil Liability Act 2002 (NSW), point-in-time metadata"
  "typed temporal reconstruction; current consolidation is not transported to another event date without proof"

claimForDamagesFromNegligence : Algebra.LegalProposition
claimForDamagesFromNegligence = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5A:claim-for-damages-from-negligence") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "part:NSW-CLA:1A")
  Negligence.auCommonLawSystem "the claim is for damages for harm resulting from negligence within s 5A(1)"

section3BExclusionApplies : Algebra.LegalProposition
section3BExclusionApplies = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3B:exclusion-applies") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "section:NSW-CLA:3B")
  Negligence.auCommonLawSystem "a relevant s 3B exclusion applies"

part1AApplies : Algebra.LegalProposition
part1AApplies = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5A:part1A-applies") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "part:NSW-CLA:1A")
  Negligence.auCommonLawSystem "Part 1A applies under the source-defined s 5A frame"

s5ARule : Algebra.LegalRule
s5ARule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5A:part1A-applicability")
  (claimForDamagesFromNegligence ∷ []) part1AApplies
  (section3BExclusionApplies ∷ []) [] nswCivilLiabilityActSourceRef
  Algebra.legislativeRuleRole "point-in-time application required" "New South Wales"

s5AClaimSource : SourceRule.PropositionSourceReceipt claimForDamagesFromNegligence
s5AClaimSource = sectionReceipt claimForDamagesFromNegligence refl "Civil Liability Act 2002 (NSW), s 5A(1)" "s5A claim-type atom"
s3BExceptionSource : SourceRule.PropositionSourceReceipt section3BExclusionApplies
s3BExceptionSource = sectionReceipt section3BExclusionApplies refl "Civil Liability Act 2002 (NSW), s 3B" "s3B exclusion atom"
s5AConclusionSource : SourceRule.PropositionSourceReceipt part1AApplies
s5AConclusionSource = sectionReceipt part1AApplies refl "Civil Liability Act 2002 (NSW), s 5A" "s5A applicability proposition"

s5ARuleSourceRealisation : SourceRule.SourceRealisedLegalRule s5ARule
s5ARuleSourceRealisation = SourceRule.source-realised-legal-rule
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef refl
  "Civil Liability Act 2002 (NSW), ss 5A, 3B"
  (legislativeRole "rule:NSW-CLA:s5A:part1A-applicability") refl refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource)
  s5AConclusionSource (s5AClaimSource Algebra.∷ Algebra.[])
  (s3BExceptionSource Algebra.∷ Algebra.[]) Algebra.[]
  nswJurisdictionPredicate nswJurisdictionSource refl
  nswCurrentTemporalPredicate nswCurrentTemporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised statutory applicability rule; negative s3B branch retained"

riskForeseeable : Algebra.LegalProposition
riskForeseeable = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:risk-foreseeable") Algebra.factualFeature
  (Ontology.stableId "risk:current") (Ontology.stableId "section:NSW-CLA:5B-1-a")
  Negligence.auCommonLawSystem "the relevant risk was foreseeable for s 5B(1)(a)"

riskNotInsignificant : Algebra.LegalProposition
riskNotInsignificant = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:risk-not-insignificant") Algebra.factualFeature
  (Ontology.stableId "risk:current") (Ontology.stableId "section:NSW-CLA:5B-1-b")
  Negligence.auCommonLawSystem "the relevant risk was not insignificant for s 5B(1)(b)"

reasonablePersonWouldTakePrecautions : Algebra.LegalProposition
reasonablePersonWouldTakePrecautions = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:reasonable-person-would-take-precautions") Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant") (Ontology.stableId "section:NSW-CLA:5B-1-c")
  Negligence.auCommonLawSystem "a reasonable person in the defendant's position would have taken the relevant precautions"

s5BThresholdOpen : Algebra.LegalProposition
s5BThresholdOpen = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:threshold-open") Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant") (Ontology.stableId "section:NSW-CLA:5B")
  Negligence.auCommonLawSystem "DASHI reconstruction: all three s 5B(1) necessary coordinates pass; this does not establish breach"

s5BThresholdRule : Algebra.LegalRule
s5BThresholdRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5B:threshold-open")
  (riskForeseeable ∷ riskNotInsignificant ∷ reasonablePersonWouldTakePrecautions ∷ [])
  s5BThresholdOpen [] [] nswCivilLiabilityActSourceRef Algebra.dashReconstructionRole
  "s 5B point-in-time text" "New South Wales"

s5BForeseeableSource : SourceRule.PropositionSourceReceipt riskForeseeable
s5BForeseeableSource = sectionReceipt riskForeseeable refl "Civil Liability Act 2002 (NSW), s 5B(1)(a)" "s5B foreseeable-risk atom"
s5BNotInsignificantSource : SourceRule.PropositionSourceReceipt riskNotInsignificant
s5BNotInsignificantSource = sectionReceipt riskNotInsignificant refl "Civil Liability Act 2002 (NSW), s 5B(1)(b)" "s5B not-insignificant atom"
s5BReasonablePrecautionsSource : SourceRule.PropositionSourceReceipt reasonablePersonWouldTakePrecautions
s5BReasonablePrecautionsSource = sectionReceipt reasonablePersonWouldTakePrecautions refl "Civil Liability Act 2002 (NSW), s 5B(1)(c), (2)" "s5B reasonable-person precautions atom"
s5BThresholdSource : SourceRule.PropositionSourceReceipt s5BThresholdOpen
s5BThresholdSource = reconstructionReceipt s5BThresholdOpen refl "Civil Liability Act 2002 (NSW), s 5B" "DASHI threshold-open reconstruction over the three statutory atoms"

s5BRuleSourceRealisation : SourceRule.SourceRealisedLegalRule s5BThresholdRule
s5BRuleSourceRealisation = SourceRule.source-realised-legal-rule
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef refl "Civil Liability Act 2002 (NSW), s 5B"
  (reconstructionRole "rule:NSW-CLA:s5B:threshold-open") refl refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource)
  s5BThresholdSource
  (s5BForeseeableSource Algebra.∷ s5BNotInsignificantSource Algebra.∷ s5BReasonablePrecautionsSource Algebra.∷ Algebra.[])
  Algebra.[] Algebra.[]
  nswJurisdictionPredicate nswJurisdictionSource refl nswCurrentTemporalPredicate nswCurrentTemporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised DASHI reconstruction of the s5B necessary-threshold conjunction"

probabilityIfNoCare : Algebra.LegalProposition
probabilityIfNoCare = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-a:probability") Algebra.factualFeature
  (Ontology.stableId "risk:current") (Ontology.stableId "factor:NSW-CLA:5B-2-a") Negligence.auCommonLawSystem "probability of harm if care were not taken is a s 5B(2)(a) consideration"
likelySeriousness : Algebra.LegalProposition
likelySeriousness = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-b:seriousness") Algebra.factualFeature
  (Ontology.stableId "harm:current") (Ontology.stableId "factor:NSW-CLA:5B-2-b") Negligence.auCommonLawSystem "likely seriousness of harm is a s 5B(2)(b) consideration"
burdenOfPrecautions : Algebra.LegalProposition
burdenOfPrecautions = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-c:burden") Algebra.factualFeature
  (Ontology.stableId "precaution:current") (Ontology.stableId "factor:NSW-CLA:5B-2-c") Negligence.auCommonLawSystem "burden of taking precautions is a s 5B(2)(c) consideration"
socialUtility : Algebra.LegalProposition
socialUtility = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-d:social-utility") Algebra.factualFeature
  (Ontology.stableId "activity:current") (Ontology.stableId "factor:NSW-CLA:5B-2-d") Negligence.auCommonLawSystem "social utility is a s 5B(2)(d) consideration"

s5BProbabilitySource : SourceRule.PropositionSourceReceipt probabilityIfNoCare
s5BProbabilitySource = sectionReceipt probabilityIfNoCare refl "Civil Liability Act 2002 (NSW), s 5B(2)(a)" "s5B probability consideration"
s5BSeriousnessSource : SourceRule.PropositionSourceReceipt likelySeriousness
s5BSeriousnessSource = sectionReceipt likelySeriousness refl "Civil Liability Act 2002 (NSW), s 5B(2)(b)" "s5B seriousness consideration"
s5BBurdenSource : SourceRule.PropositionSourceReceipt burdenOfPrecautions
s5BBurdenSource = sectionReceipt burdenOfPrecautions refl "Civil Liability Act 2002 (NSW), s 5B(2)(c)" "s5B burden consideration"
s5BSocialUtilitySource : SourceRule.PropositionSourceReceipt socialUtility
s5BSocialUtilitySource = sectionReceipt socialUtility refl "Civil Liability Act 2002 (NSW), s 5B(2)(d)" "s5B social-utility consideration"

avoidableDifferentWayAloneInsufficient : Algebra.LegalProposition
avoidableDifferentWayAloneInsufficient = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5C:different-way-alone-insufficient") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "section:NSW-CLA:5C") Negligence.auCommonLawSystem
  "mere avoidability by doing an activity differently does not of itself create or affect liability"
laterPrecautionAloneInsufficient : Algebra.LegalProposition
laterPrecautionAloneInsufficient = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5C:later-precaution-alone-insufficient") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "section:NSW-CLA:5C") Negligence.auCommonLawSystem
  "subsequent avoidance action does not of itself create or affect liability or constitute an admission"
s5CDifferentWaySource : SourceRule.PropositionSourceReceipt avoidableDifferentWayAloneInsufficient
s5CDifferentWaySource = sectionReceipt avoidableDifferentWayAloneInsufficient refl "Civil Liability Act 2002 (NSW), s 5C" "s5C different-way anti-shortcut"
s5CLaterPrecautionSource : SourceRule.PropositionSourceReceipt laterPrecautionAloneInsufficient
s5CLaterPrecautionSource = sectionReceipt laterPrecautionAloneInsufficient refl "Civil Liability Act 2002 (NSW), s 5C" "s5C later-action anti-shortcut"

negligenceNecessaryCondition : Algebra.LegalProposition
negligenceNecessaryCondition = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:factual-causation-necessary-condition") Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant") (Ontology.stableId "section:NSW-CLA:5D-1-a") Negligence.auCommonLawSystem
  "the negligence was a necessary condition of occurrence of the harm for the ordinary s 5D(1)(a) route"
scopeOfLiabilityAppropriate : Algebra.LegalProposition
scopeOfLiabilityAppropriate = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:scope-appropriate") Algebra.doctrinalPredicate
  (Ontology.stableId "harm:current") (Ontology.stableId "section:NSW-CLA:5D-1-b") Negligence.auCommonLawSystem
  "it is appropriate for the scope of liability to extend to the harm for s 5D(1)(b)"
ordinaryS5DCausationSatisfied : Algebra.LegalProposition
ordinaryS5DCausationSatisfied = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:ordinary-causation-satisfied") Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant") (Ontology.stableId "element:negligence:causation") Negligence.auCommonLawSystem
  "DASHI reconstruction: both ordinary s 5D(1) causation coordinates pass"

s5DOrdinaryRule : Algebra.LegalRule
s5DOrdinaryRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5D:ordinary-causation")
  (negligenceNecessaryCondition ∷ scopeOfLiabilityAppropriate ∷ []) ordinaryS5DCausationSatisfied
  [] [] nswCivilLiabilityActSourceRef Algebra.dashReconstructionRole
  "s 5D(1); exceptional s 5D(2) route separate" "New South Wales"

exceptionalCausationRouteRequiresSeparateReceipt : Algebra.LegalProposition
exceptionalCausationRouteRequiresSeparateReceipt = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D-2:exceptional-route-separate") Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current") (Ontology.stableId "section:NSW-CLA:5D-2") Negligence.auCommonLawSystem
  "DASHI boundary: an exceptional s 5D(2) case requires its own source-conditioned route"

s5DNecessaryConditionSource : SourceRule.PropositionSourceReceipt negligenceNecessaryCondition
s5DNecessaryConditionSource = sectionReceipt negligenceNecessaryCondition refl "Civil Liability Act 2002 (NSW), s 5D(1)(a)" "s5D factual-causation atom"
s5DScopeSource : SourceRule.PropositionSourceReceipt scopeOfLiabilityAppropriate
s5DScopeSource = sectionReceipt scopeOfLiabilityAppropriate refl "Civil Liability Act 2002 (NSW), s 5D(1)(b)" "s5D scope atom"
s5DOrdinaryConclusionSource : SourceRule.PropositionSourceReceipt ordinaryS5DCausationSatisfied
s5DOrdinaryConclusionSource = reconstructionReceipt ordinaryS5DCausationSatisfied refl "Civil Liability Act 2002 (NSW), s 5D(1)" "DASHI conjunction of the two ordinary statutory coordinates"
s5DExceptionalSource : SourceRule.PropositionSourceReceipt exceptionalCausationRouteRequiresSeparateReceipt
s5DExceptionalSource = reconstructionReceipt exceptionalCausationRouteRequiresSeparateReceipt refl "Civil Liability Act 2002 (NSW), s 5D(2)" "DASHI route-separation boundary; not verbatim statutory proposition"

s5DOrdinaryRuleSourceRealisation : SourceRule.SourceRealisedLegalRule s5DOrdinaryRule
s5DOrdinaryRuleSourceRealisation = SourceRule.source-realised-legal-rule
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef refl "Civil Liability Act 2002 (NSW), s 5D(1)"
  (reconstructionRole "rule:NSW-CLA:s5D:ordinary-causation") refl refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource)
  s5DOrdinaryConclusionSource
  (s5DNecessaryConditionSource Algebra.∷ s5DScopeSource Algebra.∷ Algebra.[])
  Algebra.[] Algebra.[]
  nswJurisdictionPredicate nswJurisdictionSource refl nswCurrentTemporalPredicate nswCurrentTemporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised DASHI reconstruction of ordinary s5D(1); s5D(2) remains separate"

underlyingTortLiabilityExcludedOrLimited : Algebra.LegalProposition
underlyingTortLiabilityExcludedOrLimited = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3C:underlying-tort-excluded-or-limited") Algebra.doctrinalPredicate
  (Ontology.stableId "tortfeasor:current") (Ontology.stableId "section:NSW-CLA:3C") Negligence.auCommonLawSystem
  "a provision of the Act excludes or limits the civil liability of a person for the tort"
correspondingVicariousLiabilityExcludedOrLimited : Algebra.LegalProposition
correspondingVicariousLiabilityExcludedOrLimited = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3C:vicarious-excluded-or-limited") Algebra.doctrinalPredicate
  (Ontology.stableId "vicarious-party:current") (Ontology.stableId "section:NSW-CLA:3C") Negligence.auCommonLawSystem
  "the same statutory exclusion or limitation operates on another person's vicarious liability for that tort"

s3CVicariousPropagationRule : Algebra.LegalRule
s3CVicariousPropagationRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s3C:vicarious-propagation")
  (underlyingTortLiabilityExcludedOrLimited ∷ []) correspondingVicariousLiabilityExcludedOrLimited
  [] [] nswCivilLiabilityActSourceRef Algebra.legislativeRuleRole
  "s 3C propagation only; does not create vicarious liability" "New South Wales"

s3CUnderlyingSource : SourceRule.PropositionSourceReceipt underlyingTortLiabilityExcludedOrLimited
s3CUnderlyingSource = sectionReceipt underlyingTortLiabilityExcludedOrLimited refl "Civil Liability Act 2002 (NSW), s 3C" "s3C underlying exclusion/limitation premise"
s3CVicariousSource : SourceRule.PropositionSourceReceipt correspondingVicariousLiabilityExcludedOrLimited
s3CVicariousSource = sectionReceipt correspondingVicariousLiabilityExcludedOrLimited refl "Civil Liability Act 2002 (NSW), s 3C" "s3C vicarious propagation conclusion"

s3CVicariousRuleSourceRealisation : SourceRule.SourceRealisedLegalRule s3CVicariousPropagationRule
s3CVicariousRuleSourceRealisation = SourceRule.source-realised-legal-rule
  nswCivilLiabilityActSource nswCivilLiabilityActSourceRef refl "Civil Liability Act 2002 (NSW), s 3C"
  (legislativeRole "rule:NSW-CLA:s3C:vicarious-propagation") refl refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource)
  s3CVicariousSource (s3CUnderlyingSource Algebra.∷ Algebra.[]) Algebra.[] Algebra.[]
  nswJurisdictionPredicate nswJurisdictionSource refl nswCurrentTemporalPredicate nswCurrentTemporalSource refl
  Negligence.auCommonLawSystem refl refl refl
  "source-realised s3C propagation rule; does not create the vicarious-liability family"

actBindsNSWCrown : Algebra.LegalProposition
actBindsNSWCrown = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s4:binds-NSW-Crown") Algebra.jurisdictionPredicate
  (Ontology.stableId "party:Crown-in-right-of-NSW") (Ontology.stableId "section:NSW-CLA:4") Negligence.auCommonLawSystem
  "the Act binds the Crown in right of New South Wales under s 4(1)"
s4CrownSource : SourceRule.PropositionSourceReceipt actBindsNSWCrown
s4CrownSource = sectionReceipt actBindsNSWCrown refl "Civil Liability Act 2002 (NSW), s 4(1)" "s4 Crown-binding proposition"

data S5BThresholdEstablishesBreach : Set where
data S5CAntiShortcutIsAbsoluteNoLiability : Set where
data S5DNecessaryConditionIsUniversalWithoutExceptionalRoute : Set where
data S3CCreatesVicariousLiability : Set where
data S4CrownBindingEstablishesCrownLiability : Set where
data SectionCitationAloneProvesCaseApplicability : Set where
data ReconstructedConjunctionIsLegislativeText : Set where

s5BThresholdDoesNotAutoEstablishBreach : S5BThresholdEstablishesBreach → ⊥
s5BThresholdDoesNotAutoEstablishBreach ()
s5CAntiShortcutDoesNotBecomeAbsoluteBlocker : S5CAntiShortcutIsAbsoluteNoLiability → ⊥
s5CAntiShortcutDoesNotBecomeAbsoluteBlocker ()
s5DOrdinaryNecessaryConditionDoesNotEraseExceptionalRoute : S5DNecessaryConditionIsUniversalWithoutExceptionalRoute → ⊥
s5DOrdinaryNecessaryConditionDoesNotEraseExceptionalRoute ()
s3CDoesNotCreateVicariousLiability : S3CCreatesVicariousLiability → ⊥
s3CDoesNotCreateVicariousLiability ()
s4DoesNotEstablishCrownLiability : S4CrownBindingEstablishesCrownLiability → ⊥
s4DoesNotEstablishCrownLiability ()
sectionCitationDoesNotProveApplicability : SectionCitationAloneProvesCaseApplicability → ⊥
sectionCitationDoesNotProveApplicability ()
reconstructedConjunctionDoesNotBecomeLegislativeText : ReconstructedConjunctionIsLegislativeText → ⊥
reconstructedConjunctionDoesNotBecomeLegislativeText ()

record NSWCivilLiabilityActAtomicBoundary : Set where
  constructor nsw-cla-atomic-boundary
  field
    section5AApplicabilitySeparated : Bool
    section5BThresholdSeparatedFromBreach : Bool
    section5CAntiShortcutsRetained : Bool
    section5DOrdinaryAndExceptionalRoutesSeparated : Bool
    section3CVicariousPropagationSeparatedFromCreation : Bool
    section4CrownScopeSeparatedFromMerits : Bool
    reconstructedRulesRemainDASHIReconstruction : Bool
    primarySourceCreatesAuthorityByCitation : Bool

canonicalNSWCivilLiabilityActAtomicBoundary : NSWCivilLiabilityActAtomicBoundary
canonicalNSWCivilLiabilityActAtomicBoundary =
  nsw-cla-atomic-boundary true true true true true true true false
