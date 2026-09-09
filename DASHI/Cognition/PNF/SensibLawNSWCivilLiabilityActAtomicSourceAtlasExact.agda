module DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact where

------------------------------------------------------------------------
-- NSW CIVIL LIABILITY ACT 2002 — PRIMARY-SOURCE ATOMIC ATLAS
--
-- Official source owner:
--   NSW Parliamentary Counsel / NSW legislation website
--   Civil Liability Act 2002 No 22 (NSW)
--   https://legislation.nsw.gov.au/view/html/inforce/current/act-2002-022
--
-- This module records source-defined atomic legal propositions.  It does not
-- convert section text into complete negligence/liability conclusions.
--
-- In particular:
--   s 5A applicability != negligence proved
--   s 5B threshold open != breach proved
--   s 5C anti-shortcut qualifier != absolute blocker
--   s 5D ordinary causation route != exhaustive causation semantics
--   s 3C vicarious propagation != creation of vicarious liability
--   s 4 Crown binding != Crown liability on the merits
------------------------------------------------------------------------

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
-- 1. Canonical primary source.
------------------------------------------------------------------------

nswCivilLiabilityActSource : Source.AttributedSource
nswCivilLiabilityActSource = Source.mkNoDOISource
  "Parliament of New South Wales; NSW Parliamentary Counsel"
  "Civil Liability Act 2002 No 22"
  "NSW legislation website — current consolidated Act"
  "2002"
  "https://legislation.nsw.gov.au/view/html/inforce/current/act-2002-022"
  Source.governmentSource
  "primary statutory text; section-level propositions below preserve exact section lineage and do not by citation alone establish applicability, breach, causation, liability or remedy"
  Source.publicAttribution

nswCivilLiabilityActLegalSource : Ontology.LegalSource
nswCivilLiabilityActLegalSource = Ontology.legalSource
  (Ontology.stableId "source:NSW:Civil-Liability-Act-2002-No22")
  Negligence.auCommonLawSystem
  Ontology.statute
  "Civil Liability Act 2002 No 22 (NSW)"
  "current consolidated source; point-in-time applicability must be separately paid"
  "New South Wales"

nswCivilLiabilityActSourceRef : Algebra.LegalSourceRef
nswCivilLiabilityActSourceRef = Algebra.legal-source-ref
  nswCivilLiabilityActLegalSource
  "Parliament of New South Wales"
  "Civil Liability Act 2002 No 22"
  "NSW Act No 22 of 2002"

nswCivilLiabilityActAuthority : Edge.SourceIdentity
nswCivilLiabilityActAuthority = Edge.source-identity
  "Parliament of New South Wales"
  "Civil Liability Act 2002 No 22"
  "NSW Act No 22 of 2002"
  Edge.legislation

legislativeRole : String → SourceRole.SourceFormRoleReceipt
legislativeRole ref = SourceRole.source-form-role-receipt
  nswCivilLiabilityActAuthority
  Ontology.statute
  Algebra.legislativeRuleRole
  ref
  true true

sectionReceipt :
  (p : Algebra.LegalProposition) →
  Negligence.auCommonLawSystem ≡ Algebra.legalSystem p →
  String → String →
  SourceRule.PropositionSourceReceipt p
sectionReceipt p system locator reference = SourceRule.proposition-source-receipt
  nswCivilLiabilityActSource
  nswCivilLiabilityActSourceRef
  locator
  SourceRule.primarySourceLayer
  (legislativeRole reference)
  system
  refl refl
  (Source.citationCreatesAuthorityIsFalse nswCivilLiabilityActSource)
  reference

------------------------------------------------------------------------
-- 2. Section 5A — application of Part 1A.
------------------------------------------------------------------------

claimForDamagesFromNegligence : Algebra.LegalProposition
claimForDamagesFromNegligence = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5A:claim-for-damages-from-negligence")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "part:NSW-CLA:1A")
  Negligence.auCommonLawSystem
  "the claim is for damages for harm resulting from negligence within the breadth described by s 5A(1)"

section3BExclusionApplies : Algebra.LegalProposition
section3BExclusionApplies = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3B:exclusion-applies")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-CLA:3B")
  Negligence.auCommonLawSystem
  "the civil liability is excluded from relevant operation of the Act by s 3B"

part1AApplies : Algebra.LegalProposition
part1AApplies = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5A:part1A-applies")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "part:NSW-CLA:1A")
  Negligence.auCommonLawSystem
  "Part 1A is applicable to the claim under the source-defined s 5A frame"

s5ARule : Algebra.LegalRule
s5ARule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5A:part1A-applicability")
  (claimForDamagesFromNegligence ∷ [])
  part1AApplies
  (section3BExclusionApplies ∷ [])
  []
  nswCivilLiabilityActSourceRef
  Algebra.legislativeRuleRole
  "current source text; point-in-time application separately required"
  "New South Wales"

------------------------------------------------------------------------
-- 3. Section 5B — failure-to-take-precautions threshold.
------------------------------------------------------------------------

riskForeseeable : Algebra.LegalProposition
riskForeseeable = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:risk-foreseeable")
  Algebra.factualFeature
  (Ontology.stableId "risk:current")
  (Ontology.stableId "section:NSW-CLA:5B-1-a")
  Negligence.auCommonLawSystem
  "the relevant risk was foreseeable for purposes of s 5B(1)(a)"

riskNotInsignificant : Algebra.LegalProposition
riskNotInsignificant = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:risk-not-insignificant")
  Algebra.factualFeature
  (Ontology.stableId "risk:current")
  (Ontology.stableId "section:NSW-CLA:5B-1-b")
  Negligence.auCommonLawSystem
  "the relevant risk was not insignificant for purposes of s 5B(1)(b)"

reasonablePersonWouldTakePrecautions : Algebra.LegalProposition
reasonablePersonWouldTakePrecautions = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:reasonable-person-would-take-precautions")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant")
  (Ontology.stableId "section:NSW-CLA:5B-1-c")
  Negligence.auCommonLawSystem
  "in the circumstances, a reasonable person in the defendant's position would have taken the relevant precautions"

s5BThresholdOpen : Algebra.LegalProposition
s5BThresholdOpen = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B:threshold-open")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant")
  (Ontology.stableId "section:NSW-CLA:5B")
  Negligence.auCommonLawSystem
  "the three source-defined s 5B(1) threshold coordinates are satisfied; this does not by itself establish breach or negligence"

s5BThresholdRule : Algebra.LegalRule
s5BThresholdRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5B:threshold-open")
  (riskForeseeable ∷ riskNotInsignificant ∷ reasonablePersonWouldTakePrecautions ∷ [])
  s5BThresholdOpen
  [] []
  nswCivilLiabilityActSourceRef
  Algebra.legislativeRuleRole
  "s 5B current statutory text"
  "New South Wales"

probabilityIfNoCare : Algebra.LegalProposition
probabilityIfNoCare = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-a:probability")
  Algebra.factualFeature
  (Ontology.stableId "risk:current")
  (Ontology.stableId "factor:NSW-CLA:5B-2-a")
  Negligence.auCommonLawSystem
  "probability of harm if care were not taken is a source-defined consideration under s 5B(2)(a)"

likelySeriousness : Algebra.LegalProposition
likelySeriousness = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-b:seriousness")
  Algebra.factualFeature
  (Ontology.stableId "harm:current")
  (Ontology.stableId "factor:NSW-CLA:5B-2-b")
  Negligence.auCommonLawSystem
  "likely seriousness of harm is a source-defined consideration under s 5B(2)(b)"

burdenOfPrecautions : Algebra.LegalProposition
burdenOfPrecautions = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-c:burden")
  Algebra.factualFeature
  (Ontology.stableId "precaution:current")
  (Ontology.stableId "factor:NSW-CLA:5B-2-c")
  Negligence.auCommonLawSystem
  "burden of taking precautions is a source-defined consideration under s 5B(2)(c)"

socialUtility : Algebra.LegalProposition
socialUtility = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5B-2-d:social-utility")
  Algebra.factualFeature
  (Ontology.stableId "activity:current")
  (Ontology.stableId "factor:NSW-CLA:5B-2-d")
  Negligence.auCommonLawSystem
  "social utility of the risk-creating activity is a source-defined consideration under s 5B(2)(d)"

------------------------------------------------------------------------
-- 4. Section 5C — anti-shortcut qualifiers.
------------------------------------------------------------------------

avoidableDifferentWayAloneInsufficient : Algebra.LegalProposition
avoidableDifferentWayAloneInsufficient = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5C:different-way-alone-insufficient")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-CLA:5C")
  Negligence.auCommonLawSystem
  "mere avoidability of the risk by doing an activity differently does not of itself create or affect liability"

laterPrecautionAloneInsufficient : Algebra.LegalProposition
laterPrecautionAloneInsufficient = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5C:later-precaution-alone-insufficient")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-CLA:5C")
  Negligence.auCommonLawSystem
  "subsequent action to avoid a similar risk does not of itself create or affect liability or constitute an admission"

------------------------------------------------------------------------
-- 5. Section 5D — ordinary causation route plus explicit exceptional frontier.
------------------------------------------------------------------------

negligenceNecessaryCondition : Algebra.LegalProposition
negligenceNecessaryCondition = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:factual-causation-necessary-condition")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant")
  (Ontology.stableId "section:NSW-CLA:5D-1-a")
  Negligence.auCommonLawSystem
  "the negligence was a necessary condition of the occurrence of the harm for the ordinary s 5D(1)(a) route"

scopeOfLiabilityAppropriate : Algebra.LegalProposition
scopeOfLiabilityAppropriate = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:scope-appropriate")
  Algebra.doctrinalPredicate
  (Ontology.stableId "harm:current")
  (Ontology.stableId "section:NSW-CLA:5D-1-b")
  Negligence.auCommonLawSystem
  "it is appropriate for the scope of the negligent person's liability to extend to the harm for the s 5D(1)(b) coordinate"

ordinaryS5DCausationSatisfied : Algebra.LegalProposition
ordinaryS5DCausationSatisfied = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D:ordinary-causation-satisfied")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:defendant")
  (Ontology.stableId "element:negligence:causation")
  Negligence.auCommonLawSystem
  "the ordinary s 5D(1) factual-causation and scope coordinates are both satisfied"

s5DOrdinaryRule : Algebra.LegalRule
s5DOrdinaryRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s5D:ordinary-causation")
  (negligenceNecessaryCondition ∷ scopeOfLiabilityAppropriate ∷ [])
  ordinaryS5DCausationSatisfied
  [] []
  nswCivilLiabilityActSourceRef
  Algebra.legislativeRuleRole
  "s 5D(1) ordinary route; s 5D(2) exceptional cases remain separate"
  "New South Wales"

exceptionalCausationRouteRequiresSeparateReceipt : Algebra.LegalProposition
exceptionalCausationRouteRequiresSeparateReceipt = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s5D-2:exceptional-route-separate")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:current")
  (Ontology.stableId "section:NSW-CLA:5D-2")
  Negligence.auCommonLawSystem
  "an exceptional causation case under s 5D(2) requires its own source-conditioned route and is not collapsed into the ordinary necessary-condition rule"

------------------------------------------------------------------------
-- 6. Sections 3C and 4 — liability propagation / Crown scope.
------------------------------------------------------------------------

underlyingTortLiabilityExcludedOrLimited : Algebra.LegalProposition
underlyingTortLiabilityExcludedOrLimited = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3C:underlying-tort-excluded-or-limited")
  Algebra.doctrinalPredicate
  (Ontology.stableId "tortfeasor:current")
  (Ontology.stableId "section:NSW-CLA:3C")
  Negligence.auCommonLawSystem
  "a provision of the Act excludes or limits the civil liability of a person for the tort"

correspondingVicariousLiabilityExcludedOrLimited : Algebra.LegalProposition
correspondingVicariousLiabilityExcludedOrLimited = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s3C:vicarious-excluded-or-limited")
  Algebra.doctrinalPredicate
  (Ontology.stableId "vicarious-party:current")
  (Ontology.stableId "section:NSW-CLA:3C")
  Negligence.auCommonLawSystem
  "the same statutory exclusion or limitation operates on another person's vicarious liability for that tort"

s3CVicariousPropagationRule : Algebra.LegalRule
s3CVicariousPropagationRule = Algebra.legal-rule
  (Ontology.stableId "rule:NSW-CLA:s3C:vicarious-propagation")
  (underlyingTortLiabilityExcludedOrLimited ∷ [])
  correspondingVicariousLiabilityExcludedOrLimited
  [] []
  nswCivilLiabilityActSourceRef
  Algebra.legislativeRuleRole
  "s 3C statutory propagation only; does not create vicarious liability"
  "New South Wales"

actBindsNSWCrown : Algebra.LegalProposition
actBindsNSWCrown = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s4:binds-NSW-Crown")
  Algebra.jurisdictionPredicate
  (Ontology.stableId "party:Crown-in-right-of-NSW")
  (Ontology.stableId "section:NSW-CLA:4")
  Negligence.auCommonLawSystem
  "the Act binds the Crown in right of New South Wales under s 4(1)"

------------------------------------------------------------------------
-- 7. Exact section-source receipts.
------------------------------------------------------------------------

s5AClaimSource = sectionReceipt claimForDamagesFromNegligence refl "Civil Liability Act 2002 (NSW), s 5A(1)" "s5A(1) application predicate"
s3BExceptionSource = sectionReceipt section3BExclusionApplies refl "Civil Liability Act 2002 (NSW), s 3B" "s3B exclusion predicate"
s5AConclusionSource = sectionReceipt part1AApplies refl "Civil Liability Act 2002 (NSW), s 5A" "s5A Part 1A applicability conclusion"

s5BForeseeableSource = sectionReceipt riskForeseeable refl "Civil Liability Act 2002 (NSW), s 5B(1)(a)" "s5B foreseeable-risk atom"
s5BNotInsignificantSource = sectionReceipt riskNotInsignificant refl "Civil Liability Act 2002 (NSW), s 5B(1)(b)" "s5B not-insignificant atom"
s5BReasonablePrecautionsSource = sectionReceipt reasonablePersonWouldTakePrecautions refl "Civil Liability Act 2002 (NSW), s 5B(1)(c), (2)" "s5B reasonable-person precautions atom"
s5BThresholdSource = sectionReceipt s5BThresholdOpen refl "Civil Liability Act 2002 (NSW), s 5B" "s5B threshold-open reconstruction bounded by the statutory necessary-condition form"

s5BProbabilitySource = sectionReceipt probabilityIfNoCare refl "Civil Liability Act 2002 (NSW), s 5B(2)(a)" "s5B probability consideration"
s5BSeriousnessSource = sectionReceipt likelySeriousness refl "Civil Liability Act 2002 (NSW), s 5B(2)(b)" "s5B seriousness consideration"
s5BBurdenSource = sectionReceipt burdenOfPrecautions refl "Civil Liability Act 2002 (NSW), s 5B(2)(c)" "s5B burden consideration"
s5BSocialUtilitySource = sectionReceipt socialUtility refl "Civil Liability Act 2002 (NSW), s 5B(2)(d)" "s5B social-utility consideration"

s5CDifferentWaySource = sectionReceipt avoidableDifferentWayAloneInsufficient refl "Civil Liability Act 2002 (NSW), s 5C" "s5C anti-shortcut qualifier"
s5CLaterPrecautionSource = sectionReceipt laterPrecautionAloneInsufficient refl "Civil Liability Act 2002 (NSW), s 5C" "s5C later-precaution anti-shortcut qualifier"

s5DNecessaryConditionSource = sectionReceipt negligenceNecessaryCondition refl "Civil Liability Act 2002 (NSW), s 5D(1)(a)" "s5D factual-causation atom"
s5DScopeSource = sectionReceipt scopeOfLiabilityAppropriate refl "Civil Liability Act 2002 (NSW), s 5D(1)(b)" "s5D scope atom"
s5DOrdinaryConclusionSource = sectionReceipt ordinaryS5DCausationSatisfied refl "Civil Liability Act 2002 (NSW), s 5D(1)" "ordinary s5D route conclusion"
s5DExceptionalSource = sectionReceipt exceptionalCausationRouteRequiresSeparateReceipt refl "Civil Liability Act 2002 (NSW), s 5D(2)" "exceptional-causation route boundary"

s3CUnderlyingSource = sectionReceipt underlyingTortLiabilityExcludedOrLimited refl "Civil Liability Act 2002 (NSW), s 3C" "s3C underlying exclusion/limitation premise"
s3CVicariousSource = sectionReceipt correspondingVicariousLiabilityExcludedOrLimited refl "Civil Liability Act 2002 (NSW), s 3C" "s3C vicarious propagation conclusion"
s4CrownSource = sectionReceipt actBindsNSWCrown refl "Civil Liability Act 2002 (NSW), s 4(1)" "s4 Crown-binding proposition"

------------------------------------------------------------------------
-- 8. Structural boundaries.
------------------------------------------------------------------------

data S5BThresholdEstablishesBreach : Set where
data S5CAntiShortcutIsAbsoluteNoLiability : Set where
data S5DNecessaryConditionIsUniversalWithoutExceptionalRoute : Set where
data S3CCreatesVicariousLiability : Set where
data S4CrownBindingEstablishesCrownLiability : Set where
data SectionCitationAloneProvesCaseApplicability : Set where

s5BThresholdDoesNotAutoEstablishBreach : S5BThresholdEstablishesBreach → ⊥
s5BThresholdDoesNotAutoEstablishBreach ()

s5CAntiShortcutDoesNotBecomeAbsoluteBlocker : S5CAntiShortcutIsAbsoluteNoLiability → ⊥
s5CAntiShortcutDoesNotBecomeAbsoluteBlocker ()

s5DOrdinaryNecessaryConditionDoesNotEraseExceptionalRoute :
  S5DNecessaryConditionIsUniversalWithoutExceptionalRoute → ⊥
s5DOrdinaryNecessaryConditionDoesNotEraseExceptionalRoute ()

s3CDoesNotCreateVicariousLiability : S3CCreatesVicariousLiability → ⊥
s3CDoesNotCreateVicariousLiability ()

s4DoesNotEstablishCrownLiability : S4CrownBindingEstablishesCrownLiability → ⊥
s4DoesNotEstablishCrownLiability ()

sectionCitationDoesNotProveApplicability : SectionCitationAloneProvesCaseApplicability → ⊥
sectionCitationDoesNotProveApplicability ()

record NSWCivilLiabilityActAtomicBoundary : Set where
  constructor nsw-cla-atomic-boundary
  field
    section5AApplicabilitySeparated : Bool
    section5BThresholdSeparatedFromBreach : Bool
    section5CAntiShortcutsRetained : Bool
    section5DOrdinaryAndExceptionalRoutesSeparated : Bool
    section3CVicariousPropagationSeparatedFromCreation : Bool
    section4CrownScopeSeparatedFromMerits : Bool
    primarySourceCreatesAuthorityByCitation : Bool

canonicalNSWCivilLiabilityActAtomicBoundary : NSWCivilLiabilityActAtomicBoundary
canonicalNSWCivilLiabilityActAtomicBoundary =
  nsw-cla-atomic-boundary true true true true true true false
