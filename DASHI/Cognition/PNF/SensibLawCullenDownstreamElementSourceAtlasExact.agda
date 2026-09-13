module DASHI.Cognition.PNF.SensibLawCullenDownstreamElementSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as PrimarySources
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact as Edelman64
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Vicarious

------------------------------------------------------------------------
-- CULLEN DOWNSTREAM ELEMENT SOURCE ATLAS
--
-- Duty and breach are different elements of the same negligence WrongType.
-- Edelman [64] is retained for the duty route.  The joint reasons at [48] are
-- retained separately for the breach disposition.  The vicarious family is now
-- independently source-paid by the 1983 Act + Cullen [100].
------------------------------------------------------------------------

cullenPrimarySource : Source.AttributedSource
cullenPrimarySource = PrimarySources.cullenHCA19

joint48Locator : String
joint48Locator = "Cullen v New South Wales [2026] HCA 19, joint reasons [48]"

joint48BreachNotEstablished : Algebra.LegalProposition
joint48BreachNotEstablished = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:joint:48:breach-not-established")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "element:negligence:breach")
  Negligence.auCommonLawSystem
  "the appellant did not establish breach of the duty of care"

joint48BreachAttachment :
  Downstream.PrimarySourceAttachment Downstream.wrongElementEvaluationStage
joint48BreachAttachment =
  Downstream.primary-source-attachment
    cullenPrimarySource joint48Locator joint48BreachNotEstablished
    "Joint reasons [48] are attached to the breach-element disposition only; the citation does not itself define general breach doctrine, create authority or determine another element."
    (Source.citationCreatesAuthorityIsFalse cullenPrimarySource)

------------------------------------------------------------------------
-- Compatibility surface only.
--
-- This old `WrongElementPrimarySource` shape predates the atomic split between
-- test-definition source and case-outcome source.  It remains for downstream
-- compatibility, but is NOT the canonical source-conditioned breach definition.
-- The canonical route is the NSW CLA atomic test-definition atlas plus Cullen
-- case-outcome evidence.
------------------------------------------------------------------------

cullenBreachElementDefinitionSource :
  Downstream.WrongElementPrimarySource Negligence.breachElement
cullenBreachElementDefinitionSource =
  Downstream.wrongelement-primary-source
    (Downstream.primary-source-attachment
      cullenPrimarySource joint48Locator joint48BreachNotEstablished
      "LEGACY COMPATIBILITY ONLY: Cullen [48] supplies the case breach disposition, not the general breach-test definition. Use the atomic NSW CLA source atlas for governing test semantics."
      (Source.citationCreatesAuthorityIsFalse cullenPrimarySource))
    refl "element:negligence:breach" joint48Locator

cullenBreachEvaluation : Legal.WrongElementEvaluation
cullenBreachEvaluation = Legal.wrongElementEvaluation
  (Ontology.WrongType.wrongTypeId Negligence.negligenceWrongType)
  "element:negligence:breach"
  Legal.elementUnsatisfied
  (joint48Locator ∷ [])
  "source-attributed Cullen joint-reasons breach evaluation"

cullenSourceAttributedBreachEvaluation :
  Downstream.SourceAttributedElementEvaluation Negligence.breachElement
cullenSourceAttributedBreachEvaluation =
  Downstream.source-attributed-element-evaluation
    cullenBreachElementDefinitionSource
    cullenBreachEvaluation refl
    (joint48BreachAttachment ∷ [])
    "Legacy projection of Cullen breach outcome. Canonical atomic semantics separate statutory/common-law test definition from [48] outcome evidence."

------------------------------------------------------------------------
-- Liability-family frontier is now source-paid, but merits remain independent.
------------------------------------------------------------------------

data CullenLiabilityFamilyFrontier : Set where
  liabilityFamilyUnresolved : CullenLiabilityFamilyFrontier
  liabilityFamilySourcePaid : Downstream.LiabilityFamily → CullenLiabilityFamilyFrontier

currentCullenLiabilityFamilyFrontier : CullenLiabilityFamilyFrontier
currentCullenLiabilityFamilyFrontier =
  liabilityFamilySourcePaid Downstream.vicariousLiability

cullenFamilyPaymentReceipt : Vicarious.CullenVicariousFamilyReceipt
cullenFamilyPaymentReceipt = Vicarious.cullenVicariousFamilyReceipt

data DutySourcePaysBreach : Set where
data BreachDispositionDeterminesLiabilityFamily : Set where
data NoBreachFindingDefinesGeneralBreachDoctrine : Set where
data SameJudgmentCollapsesElementSourceRoles : Set where
data VicariousFamilyPaymentEstablishesUnderlyingTort : Set where
data LegacyBreachDefinitionAttachmentIsCanonicalAtomicDefinition : Set where

dutySourceDoesNotPayBreach : DutySourcePaysBreach → ⊥
dutySourceDoesNotPayBreach ()

breachDoesNotDetermineLiabilityFamily : BreachDispositionDeterminesLiabilityFamily → ⊥
breachDoesNotDetermineLiabilityFamily ()

caseDispositionDoesNotDefineAllBreachDoctrine : NoBreachFindingDefinesGeneralBreachDoctrine → ⊥
caseDispositionDoesNotDefineAllBreachDoctrine ()

sameJudgmentDoesNotCollapseElementRoles : SameJudgmentCollapsesElementSourceRoles → ⊥
sameJudgmentDoesNotCollapseElementRoles ()

familyPaymentDoesNotEstablishTort : VicariousFamilyPaymentEstablishesUnderlyingTort → ⊥
familyPaymentDoesNotEstablishTort ()

legacyBreachDefinitionAttachmentIsNotCanonicalAtomicDefinition :
  LegacyBreachDefinitionAttachmentIsCanonicalAtomicDefinition → ⊥
legacyBreachDefinitionAttachmentIsNotCanonicalAtomicDefinition ()

cullenDownstreamReading : String
cullenDownstreamReading =
  "Cullen retains separate [64] duty and [48] breach-outcome sources. The liability-family frontier is independently source-paid as vicarious liability by the Law Reform (Vicarious Liability) Act 1983 (NSW) plus Cullen [100]. This family classification does not establish the underlying negligence violation; the legacy breach-definition attachment is projection-only and the atomic statutory/common-law definition/outcome split is canonical."
