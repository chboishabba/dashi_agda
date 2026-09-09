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

------------------------------------------------------------------------
-- CULLEN DOWNSTREAM ELEMENT SOURCE ATLAS
--
-- Duty and breach are different elements of the same negligence WrongType.
-- Edelman [64] is retained for the duty route.  The joint reasons at [48] are
-- retained separately for the breach disposition.  Neither source attachment
-- silently pays the other element or a later liability classification.
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
    cullenPrimarySource
    joint48Locator
    joint48BreachNotEstablished
    "Joint reasons [48] are attached to the breach-element disposition only; the citation does not itself create authority or determine another element."
    (Source.citationCreatesAuthorityIsFalse cullenPrimarySource)

cullenBreachElementDefinitionSource :
  Downstream.WrongElementPrimarySource Negligence.breachElement
cullenBreachElementDefinitionSource =
  Downstream.wrongelement-primary-source
    (Downstream.primary-source-attachment
      cullenPrimarySource
      joint48Locator
      joint48BreachNotEstablished
      "Cullen [48] is retained as a primary source relevant to the concrete breach element in this case; generic breach doctrine may require additional sources."
      (Source.citationCreatesAuthorityIsFalse cullenPrimarySource))
    refl
    "element:negligence:breach"
    joint48Locator

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
    cullenBreachEvaluation
    refl
    (joint48BreachAttachment ∷ [])
    "Cullen breach element evaluated separately from the Edelman [64] duty route."

------------------------------------------------------------------------
-- Liability-family frontier.
--
-- The generic downstream discipline has typed families, but this module does
-- not guess which one pays the State/NSW liability consumer.  That must be read
-- from an exact primary source and its applicable statutory/common-law frame.
------------------------------------------------------------------------

data CullenLiabilityFamilyFrontier : Set where
  liabilityFamilyUnresolved : CullenLiabilityFamilyFrontier
  liabilityFamilySourcePaid : Downstream.LiabilityFamily → CullenLiabilityFamilyFrontier

currentCullenLiabilityFamilyFrontier : CullenLiabilityFamilyFrontier
currentCullenLiabilityFamilyFrontier = liabilityFamilyUnresolved

data DutySourcePaysBreach : Set where
data BreachDispositionDeterminesLiabilityFamily : Set where
data NoBreachFindingDefinesGeneralBreachDoctrine : Set where
data SameJudgmentCollapsesElementSourceRoles : Set where

dutySourceDoesNotPayBreach : DutySourcePaysBreach → ⊥
dutySourceDoesNotPayBreach ()

breachDoesNotDetermineLiabilityFamily :
  BreachDispositionDeterminesLiabilityFamily → ⊥
breachDoesNotDetermineLiabilityFamily ()

caseDispositionDoesNotDefineAllBreachDoctrine :
  NoBreachFindingDefinesGeneralBreachDoctrine → ⊥
caseDispositionDoesNotDefineAllBreachDoctrine ()

sameJudgmentDoesNotCollapseElementRoles :
  SameJudgmentCollapsesElementSourceRoles → ⊥
sameJudgmentDoesNotCollapseElementSourceRoles ()

cullenDownstreamReading : String
cullenDownstreamReading =
  "Cullen now carries separate primary-source attachments for the Edelman [64] duty route and joint-reasons [48] breach disposition. Breach is unsatisfied on the encoded [48] case disposition, but liability-family classification remains unresolved until independently source-paid."
