module DASHI.Cognition.PNF.SensibLawCullenAtomicSourceConditionedDutyBreachExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as PrimarySources
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as Implication
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Routes
import DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact as Edelman64
import DASHI.Cognition.PNF.SensibLawCullenDownstreamElementSourceAtlasExact as CullenElements

------------------------------------------------------------------------
-- 1. Source-container identity stays separate from proposition role.
------------------------------------------------------------------------

cullenAuthorityIdentity : Edge.SourceIdentity
cullenAuthorityIdentity = Edge.source-identity
  "High Court of Australia"
  "Cullen v New South Wales"
  "[2026] HCA 19"
  Edge.bindingPrecedent

cullenReconstructionRole : String → SourceRole.SourceFormRoleReceipt
cullenReconstructionRole reference = SourceRole.source-form-role-receipt
  cullenAuthorityIdentity
  Ontology.caseLaw
  Algebra.dashReconstructionRole
  reference
  true
  true

cullenBindingRatioRole : String → SourceRole.SourceFormRoleReceipt
cullenBindingRatioRole reference = SourceRole.source-form-role-receipt
  cullenAuthorityIdentity
  Ontology.caseLaw
  Algebra.bindingRatioRole
  reference
  true
  true

cullenReconstructionReceipt :
  (p : Algebra.LegalProposition) →
  Negligence.auCommonLawSystem ≡ Algebra.legalSystem p →
  String → String →
  SourceRule.PropositionSourceReceipt p
cullenReconstructionReceipt p system locator reference =
  SourceRule.proposition-source-receipt
    PrimarySources.cullenHCA19
    Routes.cullenSource
    locator
    SourceRule.repositoryReconstructionLayer
    (cullenReconstructionRole reference)
    system
    refl
    refl
    (Source.citationCreatesAuthorityIsFalse PrimarySources.cullenHCA19)
    reference

cullenPrimaryRatioReceipt :
  (p : Algebra.LegalProposition) →
  Negligence.auCommonLawSystem ≡ Algebra.legalSystem p →
  String → String →
  SourceRule.PropositionSourceReceipt p
cullenPrimaryRatioReceipt p system locator reference =
  SourceRule.proposition-source-receipt
    PrimarySources.cullenHCA19
    Routes.cullenSource
    locator
    SourceRule.primarySourceLayer
    (cullenBindingRatioRole reference)
    system
    refl
    refl
    (Source.citationCreatesAuthorityIsFalse PrimarySources.cullenHCA19)
    reference

------------------------------------------------------------------------
-- 2. The source-correct Edelman rule remains explicitly DASHI reconstruction.
--
-- Its three premises are reconstructed propositions.  Direct [64] propositions
-- can be used as case-level atomic outcome evidence, but they are not silently
-- identified with the reconstructed premises.
------------------------------------------------------------------------

cullenJurisdictionPredicate : Algebra.LegalProposition
cullenJurisdictionPredicate = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:atomic:jurisdiction")
  Algebra.jurisdictionPredicate
  (Ontology.stableId "case:Cullen")
  (Ontology.stableId "court:High-Court-of-Australia")
  Negligence.auCommonLawSystem
  "the Cullen negligence duty reconstruction is evaluated inside its Australian High Court / NSW legal-system scope"

cullenTemporalPredicate : Algebra.LegalProposition
cullenTemporalPredicate = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:atomic:temporal")
  Algebra.temporalPredicate
  (Ontology.stableId "case:Cullen")
  (Ontology.stableId "date:2026-06-17")
  Negligence.auCommonLawSystem
  "the encoded Cullen source state is evaluated at the 17 June 2026 judgment date; later treatment is a separate coordinate"

positiveRiskSource : SourceRule.PropositionSourceReceipt Routes.positiveRiskCreatingActs
positiveRiskSource = cullenReconstructionReceipt
  Routes.positiveRiskCreatingActs refl Edelman64.edelman64Locator
  "DASHI reconstruction of the positive-risk-creating-acts premise from the retained Edelman [64] source proposition"

ordinaryDutyAnalysisSource :
  SourceRule.PropositionSourceReceipt Routes.ordinaryCommonLawDutyAnalysis
ordinaryDutyAnalysisSource = cullenReconstructionReceipt
  Routes.ordinaryCommonLawDutyAnalysis refl Edelman64.edelman64Locator
  "DASHI reconstruction of the ordinary-common-law-duty-analysis premise from Edelman [64]"

noPowerRequirementSource :
  SourceRule.PropositionSourceReceipt Routes.statutoryPowerNotRequiredOnEdelmanRoute
noPowerRequirementSource = cullenReconstructionReceipt
  Routes.statutoryPowerNotRequiredOnEdelmanRoute refl Edelman64.edelman64Locator
  "DASHI reconstruction: no statutory-power invocation is not textually identical to the stronger no-power-requirement route proposition"

cullenDutyConclusionSource :
  SourceRule.PropositionSourceReceipt Routes.cullenDutyProposition
cullenDutyConclusionSource = cullenReconstructionReceipt
  Routes.cullenDutyProposition refl Edelman64.edelman64Locator
  "source-reviewed Cullen duty conclusion used by the DASHI Edelman route; the compiled implication remains repository reconstruction"

cullenJurisdictionSource :
  SourceRule.PropositionSourceReceipt cullenJurisdictionPredicate
cullenJurisdictionSource = cullenReconstructionReceipt
  cullenJurisdictionPredicate refl
  "Cullen v New South Wales [2026] HCA 19, source/case metadata"
  "DASHI typed jurisdiction predicate reconstructed from the canonical HCA source identity"

cullenTemporalSource :
  SourceRule.PropositionSourceReceipt cullenTemporalPredicate
cullenTemporalSource = cullenReconstructionReceipt
  cullenTemporalPredicate refl
  "Cullen v New South Wales [2026] HCA 19, judgment metadata"
  "DASHI typed temporal predicate reconstructed from the canonical judgment date; later treatment not inferred"

cullenEdelmanRuleSourceRealisation :
  SourceRule.SourceRealisedLegalRule Routes.edelmanDutyRule
cullenEdelmanRuleSourceRealisation = SourceRule.source-realised-legal-rule
  PrimarySources.cullenHCA19
  Routes.cullenSource
  refl
  Edelman64.edelman64Locator
  (cullenReconstructionRole "rule:Cullen:Edelman-source-correct-duty-route")
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse PrimarySources.cullenHCA19)
  cullenDutyConclusionSource
  (positiveRiskSource Algebra.∷ ordinaryDutyAnalysisSource Algebra.∷
   noPowerRequirementSource Algebra.∷ Algebra.[])
  Algebra.[]
  Algebra.[]
  cullenJurisdictionPredicate
  cullenJurisdictionSource
  refl
  cullenTemporalPredicate
  cullenTemporalSource
  refl
  Negligence.auCommonLawSystem
  refl refl refl
  "source-realised DASHI reconstruction of the retained Edelman duty route"

------------------------------------------------------------------------
-- 3. Direct paragraph-level source receipts are required as OUTCOME evidence.
--
-- We intentionally do not guess the proposition-level authority role of each
-- [64] sentence here.  Callers must pay canonical PropositionSourceReceipts and
-- prove that they are primary, from Cullen, and from the exact paragraph.
------------------------------------------------------------------------

record Edelman64DirectAtomicSources : Set₁ where
  constructor edelman64-direct-atomic-sources
  field
    positiveActsDirectSource :
      SourceRule.PropositionSourceReceipt Edelman64.edelman64PositiveActsCreatingRisk
    positiveActsPrimary :
      SourceRule.attributionLayer positiveActsDirectSource ≡ SourceRule.primarySourceLayer
    positiveActsCullen :
      SourceRule.attributedSource positiveActsDirectSource ≡ PrimarySources.cullenHCA19
    positiveActsExactLocator :
      SourceRule.exactLocator positiveActsDirectSource ≡ Edelman64.edelman64Locator

    ordinaryDutyDirectSource :
      SourceRule.PropositionSourceReceipt Edelman64.edelman64OrdinaryCommonLawDuty
    ordinaryDutyPrimary :
      SourceRule.attributionLayer ordinaryDutyDirectSource ≡ SourceRule.primarySourceLayer
    ordinaryDutyCullen :
      SourceRule.attributedSource ordinaryDutyDirectSource ≡ PrimarySources.cullenHCA19
    ordinaryDutyExactLocator :
      SourceRule.exactLocator ordinaryDutyDirectSource ≡ Edelman64.edelman64Locator

    noPowerDirectSource :
      SourceRule.PropositionSourceReceipt Edelman64.edelman64NoStatutoryPowerInvocation
    noPowerPrimary :
      SourceRule.attributionLayer noPowerDirectSource ≡ SourceRule.primarySourceLayer
    noPowerCullen :
      SourceRule.attributedSource noPowerDirectSource ≡ PrimarySources.cullenHCA19
    noPowerExactLocator :
      SourceRule.exactLocator noPowerDirectSource ≡ Edelman64.edelman64Locator

open Edelman64DirectAtomicSources public

positiveRiskOutcome :
  Edelman64DirectAtomicSources → Atomic.AtomicOutcomeSource Routes.positiveRiskCreatingActs
positiveRiskOutcome sources = Atomic.atomic-outcome-source
  Edelman64.edelman64PositiveActsCreatingRisk
  (positiveActsDirectSource sources)
  (Algebra.propositionId Routes.positiveRiskCreatingActs)
  refl refl
  "direct [64] positive-acts proposition is retained as sourced outcome evidence for the reconstructed positive-risk-creating-acts atom"

ordinaryDutyOutcome :
  Edelman64DirectAtomicSources → Atomic.AtomicOutcomeSource Routes.ordinaryCommonLawDutyAnalysis
ordinaryDutyOutcome sources = Atomic.atomic-outcome-source
  Edelman64.edelman64OrdinaryCommonLawDuty
  (ordinaryDutyDirectSource sources)
  (Algebra.propositionId Routes.ordinaryCommonLawDutyAnalysis)
  refl refl
  "direct [64] ordinary-duty proposition is retained as sourced outcome evidence for the reconstructed doctrinal atom"

noPowerOutcome :
  Edelman64DirectAtomicSources →
  Atomic.AtomicOutcomeSource Routes.statutoryPowerNotRequiredOnEdelmanRoute
noPowerOutcome sources = Atomic.atomic-outcome-source
  Edelman64.edelman64NoStatutoryPowerInvocation
  (noPowerDirectSource sources)
  (Algebra.propositionId Routes.statutoryPowerNotRequiredOnEdelmanRoute)
  refl refl
  "direct no-power-invocation proposition is evidence for the DASHI reconstruction; it is not identified with the stronger route proposition"

------------------------------------------------------------------------
-- 4. Positive atomic helper.  Fits is the independently attributed outcome
-- receipt itself; FailsToFit is empty in this positive fixture.
------------------------------------------------------------------------

data NoAtomicFailure : Set where

positiveAtomicTest :
  ∀ {p} →
  SourceRule.PropositionSourceReceipt p →
  Atomic.AtomicOutcomeSource p →
  Atomic.SourceConditionedAtomicLegalTest p
positiveAtomicTest definitionSource outcome = Atomic.source-conditioned-atomic-legal-test
  definitionSource
  (Algebra.subjectReference _)
  refl
  (Atomic.AtomicOutcomeSource _)
  NoAtomicFailure
  (λ fit ())
  (λ fit → fit)
  (λ ())
  BT.pos
  (λ _ → outcome)
  (λ ())
  "positive source-conditioned atomic Cullen fixture"

positiveRiskAtom :
  Edelman64DirectAtomicSources →
  Atomic.SourceConditionedAtomicLegalTest Routes.positiveRiskCreatingActs
positiveRiskAtom sources = positiveAtomicTest positiveRiskSource (positiveRiskOutcome sources)

ordinaryDutyAtom :
  Edelman64DirectAtomicSources →
  Atomic.SourceConditionedAtomicLegalTest Routes.ordinaryCommonLawDutyAnalysis
ordinaryDutyAtom sources = positiveAtomicTest ordinaryDutyAnalysisSource (ordinaryDutyOutcome sources)

noPowerRequirementAtom :
  Edelman64DirectAtomicSources →
  Atomic.SourceConditionedAtomicLegalTest Routes.statutoryPowerNotRequiredOnEdelmanRoute
noPowerRequirementAtom sources = positiveAtomicTest noPowerRequirementSource (noPowerOutcome sources)

jurisdictionOutcome : Atomic.AtomicOutcomeSource cullenJurisdictionPredicate
jurisdictionOutcome = Atomic.atomic-outcome-source
  cullenJurisdictionPredicate cullenJurisdictionSource
  (Algebra.propositionId cullenJurisdictionPredicate) refl refl
  "typed jurisdiction reconstruction is the sourced case-level outcome evidence for this atomic scope gate"

jurisdictionAtom : Atomic.SourceConditionedAtomicLegalTest cullenJurisdictionPredicate
jurisdictionAtom = positiveAtomicTest cullenJurisdictionSource jurisdictionOutcome

temporalOutcome : Atomic.AtomicOutcomeSource cullenTemporalPredicate
temporalOutcome = Atomic.atomic-outcome-source
  cullenTemporalPredicate cullenTemporalSource
  (Algebra.propositionId cullenTemporalPredicate) refl refl
  "typed judgment-date reconstruction is the sourced case-level outcome evidence for this atomic temporal gate"

temporalAtom : Atomic.SourceConditionedAtomicLegalTest cullenTemporalPredicate
temporalAtom = positiveAtomicTest cullenTemporalSource temporalOutcome

------------------------------------------------------------------------
-- 5. Graph derivation stays a different currency from atomic fit.
------------------------------------------------------------------------

cullenEdelmanAtomicFacts : Algebra.FactSet
cullenEdelmanAtomicFacts = Algebra.fact-set
  (Routes.positiveRiskCreatingActs ∷
   Routes.ordinaryCommonLawDutyAnalysis ∷
   Routes.statutoryPowerNotRequiredOnEdelmanRoute ∷
   cullenJurisdictionPredicate ∷
   cullenTemporalPredicate ∷ [])

positiveRiskDerived :
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) Routes.positiveRiskCreatingActs
positiveRiskDerived = Algebra.fromFact Algebra.here

ordinaryDutyDerived :
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) Routes.ordinaryCommonLawDutyAnalysis
ordinaryDutyDerived = Algebra.fromFact (Algebra.there Algebra.here)

noPowerDerived :
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) Routes.statutoryPowerNotRequiredOnEdelmanRoute
noPowerDerived = Algebra.fromFact (Algebra.there (Algebra.there Algebra.here))

jurisdictionDerived :
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) cullenJurisdictionPredicate
jurisdictionDerived = Algebra.fromFact
  (Algebra.there (Algebra.there (Algebra.there Algebra.here)))

temporalDerived :
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) cullenTemporalPredicate
temporalDerived = Algebra.fromFact
  (Algebra.there (Algebra.there (Algebra.there (Algebra.there Algebra.here))))

edelmanPremiseAtom :
  Edelman64DirectAtomicSources →
  ∀ {p} →
  p Algebra.∈ Algebra.premises Routes.edelmanDutyRule →
  Atomic.SourceConditionedAtomicLegalTest p
edelmanPremiseAtom sources Algebra.here = positiveRiskAtom sources
edelmanPremiseAtom sources (Algebra.there Algebra.here) = ordinaryDutyAtom sources
edelmanPremiseAtom sources (Algebra.there (Algebra.there Algebra.here)) = noPowerRequirementAtom sources

edelmanPremiseSourceExact :
  (sources : Edelman64DirectAtomicSources) →
  ∀ {p} (membership : p Algebra.∈ Algebra.premises Routes.edelmanDutyRule) →
  Atomic.sourceReceipt (edelmanPremiseAtom sources membership)
  ≡ Implication.lookupAll
      (SourceRule.premiseSources cullenEdelmanRuleSourceRealisation)
      membership
edelmanPremiseSourceExact sources Algebra.here = refl
edelmanPremiseSourceExact sources (Algebra.there Algebra.here) = refl
edelmanPremiseSourceExact sources (Algebra.there (Algebra.there Algebra.here)) = refl

edelmanPremisePasses :
  (sources : Edelman64DirectAtomicSources) →
  ∀ {p} (membership : p Algebra.∈ Algebra.premises Routes.edelmanDutyRule) →
  Atomic.gate (edelmanPremiseAtom sources membership) ≡ BT.pos
edelmanPremisePasses sources Algebra.here = refl
edelmanPremisePasses sources (Algebra.there Algebra.here) = refl
edelmanPremisePasses sources (Algebra.there (Algebra.there Algebra.here)) = refl

edelmanPremiseDerived :
  ∀ {p} →
  p Algebra.∈ Algebra.premises Routes.edelmanDutyRule →
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) p
edelmanPremiseDerived Algebra.here = positiveRiskDerived
edelmanPremiseDerived (Algebra.there Algebra.here) = ordinaryDutyDerived
edelmanPremiseDerived (Algebra.there (Algebra.there Algebra.here)) = noPowerDerived

cullenEdelmanAtomicImplication :
  Edelman64DirectAtomicSources →
  Implication.SourceConditionedAtomicLegalImplication
    Routes.cullenSourceCorrectGraph
    cullenEdelmanAtomicFacts
    (λ _ → ⊤)
    Routes.edelmanDutyRule
cullenEdelmanAtomicImplication sources =
  Implication.source-conditioned-atomic-legal-implication
    (Algebra.there Algebra.here)
    tt
    cullenEdelmanRuleSourceRealisation
    (edelmanPremiseAtom sources)
    (edelmanPremiseSourceExact sources)
    (edelmanPremisePasses sources)
    edelmanPremiseDerived
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    jurisdictionAtom
    refl
    refl
    jurisdictionDerived
    temporalAtom
    refl
    refl
    temporalDerived
    "Cullen Edelman [64] atomic source-conditioned DASHI duty implication"

cullenEdelmanAtomicDerivationReceipt :
  (sources : Edelman64DirectAtomicSources) →
  Implication.AtomicImplicationDerivationReceipt
    (cullenEdelmanAtomicImplication sources)
cullenEdelmanAtomicDerivationReceipt sources =
  Implication.atomic-implication-derivation-receipt
    (positiveRiskDerived Algebra.∷ ordinaryDutyDerived Algebra.∷
     noPowerDerived Algebra.∷ Algebra.[])
    Algebra.[]
    Algebra.[]

cullenDutyDerivedAtomically :
  (sources : Edelman64DirectAtomicSources) →
  Algebra.Derivation Routes.cullenSourceCorrectGraph cullenEdelmanAtomicFacts
    (λ _ → ⊤) Routes.cullenDutyProposition
cullenDutyDerivedAtomically sources =
  Implication.compileAtomicLegalImplication
    (cullenEdelmanAtomicImplication sources)
    (cullenEdelmanAtomicDerivationReceipt sources)

------------------------------------------------------------------------
-- 6. Breach: primary [48] provides FAILURE OUTCOME, not the breach definition.
------------------------------------------------------------------------

cullenBreachEstablished : Algebra.LegalProposition
cullenBreachEstablished = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:breach-established-atomic-test")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "element:negligence:breach")
  Negligence.auCommonLawSystem
  "breach of the applicable Cullen duty is established on the legally governing breach test"

joint48FailureSource :
  SourceRule.PropositionSourceReceipt CullenElements.joint48BreachNotEstablished
joint48FailureSource = cullenPrimaryRatioReceipt
  CullenElements.joint48BreachNotEstablished refl
  CullenElements.joint48Locator
  "joint reasons [48] breach disposition; used only as case-specific failure evidence"

joint48BreachFailureOutcome : Atomic.AtomicOutcomeSource cullenBreachEstablished
joint48BreachFailureOutcome = Atomic.atomic-outcome-source
  CullenElements.joint48BreachNotEstablished
  joint48FailureSource
  (Algebra.propositionId cullenBreachEstablished)
  refl refl
  "[48] positively states that breach was not established; this pays the negative outcome on the Cullen breach-established atom but does not define the general breach test"

data NoCullenBreachFitWitness : Set where

cullenBreachFailureAtom :
  SourceRule.PropositionSourceReceipt cullenBreachEstablished →
  Atomic.SourceConditionedAtomicLegalTest cullenBreachEstablished
cullenBreachFailureAtom breachDefinitionSource =
  Atomic.source-conditioned-atomic-legal-test
    breachDefinitionSource
    (Algebra.subjectReference cullenBreachEstablished)
    refl
    NoCullenBreachFitWitness
    (Atomic.AtomicOutcomeSource cullenBreachEstablished)
    (λ () failure)
    (λ ())
    (λ failure → failure)
    BT.neg
    (λ ())
    (λ _ → joint48BreachFailureOutcome)
    "Cullen breach atom: negative means sourced failure of this exact breach test, not proof of an opposite wrong"

------------------------------------------------------------------------
-- 7. The remaining breach coordinate is therefore exact and source-directed.
------------------------------------------------------------------------

record CullenBreachDefinitionSourceDemand : Set₁ where
  constructor cullen-breach-definition-source-demand
  field
    governingBreachTest : Algebra.LegalProposition
    governingBreachTestIsCullenAtom : governingBreachTest ≡ cullenBreachEstablished
    governingDefinitionSource :
      SourceRule.PropositionSourceReceipt governingBreachTest
    definitionMustComeFromApplicableLawNotDispositionAlone : Bool
    demandReference : String

open CullenBreachDefinitionSourceDemand public

installCullenBreachFailureAtom :
  CullenBreachDefinitionSourceDemand →
  Atomic.SourceConditionedAtomicLegalTest cullenBreachEstablished
installCullenBreachFailureAtom demand with governingBreachTestIsCullenAtom demand
... | refl = cullenBreachFailureAtom (governingDefinitionSource demand)

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data Edelman64DirectFactIsDASHIRule : Set where
data CullenReconstructionIsBindingRatio : Set where
data Cullen48FailureDefinesGeneralBreachStandard : Set where
data CullenBreachFailureMeansOppositeWrong : Set where
data DutyPositiveAtomsAutomaticallyPayBreach : Set where

edelmanDirectFactDoesNotBecomeDASHIRule : Edelman64DirectFactIsDASHIRule → ⊥
edelmanDirectFactDoesNotBecomeDASHIRule ()

reconstructionDoesNotBecomeBindingRatio : CullenReconstructionIsBindingRatio → ⊥
reconstructionDoesNotBecomeBindingRatio ()

caseFailureDoesNotDefineGeneralBreachStandard :
  Cullen48FailureDefinesGeneralBreachStandard → ⊥
caseFailureDoesNotDefineGeneralBreachStandard ()

breachFailureDoesNotMeanOppositeWrong :
  CullenBreachFailureMeansOppositeWrong → ⊥
breachFailureDoesNotMeanOppositeWrong ()

dutyAtomsDoNotPayBreach : DutyPositiveAtomsAutomaticallyPayBreach → ⊥
dutyAtomsDoNotPayBreach ()

record CullenAtomicDutyBreachBoundary : Set where
  constructor cullen-atomic-duty-breach-boundary
  field
    dutyRuleRemainsReconstruction : Bool
    directParagraphSourcesRequiredForPositiveAtoms : Bool
    atomicFitAndGraphDerivationBothRequired : Bool
    breachFailureHasPrimaryOutcomeSource : Bool
    breachFailureSourceDefinesGeneralBreachTest : Bool
    negativeBreachMeansOppositeWrong : Bool

canonicalCullenAtomicDutyBreachBoundary : CullenAtomicDutyBreachBoundary
canonicalCullenAtomicDutyBreachBoundary =
  cullen-atomic-duty-breach-boundary true true true true false false
