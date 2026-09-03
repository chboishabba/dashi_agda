module DASHI.Culture.LopezRiosFourContradictionsTypedBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact as Sources
import DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact as Psych

------------------------------------------------------------------------
-- FOUR CONTRADICTIONS: SOURCE LABELS VERSUS DASHI FORMAL TRANSLATIONS
--
-- The constructor names below are a bounded transcription of the four
-- contradiction classes named by Lopez-Rios (2022). The interpretation of
-- those classes as exact DASHI predicates is explicitly separate and marked
-- as reconstruction/extension.
------------------------------------------------------------------------

data LopezRiosContradictionClass : Set where
  antiDialecticalIdealist
  apoliticalNeutrality
  servilityToExistingRelations
  psychologisingMystification
  : LopezRiosContradictionClass

record SourceNamedContradiction : Set where
  constructor source-named-contradiction
  field
    contradictionClass : LopezRiosContradictionClass
    sourceAtlas : Sources.lopezRiosSourceAtlas ≡ Sources.lopezRiosSourceAtlas

open SourceNamedContradiction public

sourceAntiDialectical : SourceNamedContradiction
sourceAntiDialectical = source-named-contradiction antiDialecticalIdealist refl

sourceApolitical : SourceNamedContradiction
sourceApolitical = source-named-contradiction apoliticalNeutrality refl

sourceServility : SourceNamedContradiction
sourceServility = source-named-contradiction servilityToExistingRelations refl

sourcePsychologisation : SourceNamedContradiction
sourcePsychologisation = source-named-contradiction psychologisingMystification refl

------------------------------------------------------------------------
-- DASHI reconstruction: intervention can alter the individual coordinate while
-- preserving the structural coordinate. Improvement of one projected outcome
-- therefore does not, by itself, certify structural resolution.
------------------------------------------------------------------------

data StructureState : Set where
  structureUnchanged : StructureState

data IndividualState : Set where
  distressed adapted : IndividualState

record SocialPsychState : Set where
  constructor social-psych-state
  field
    structure : StructureState
    individual : IndividualState

open SocialPsychState public

before : SocialPsychState
before = social-psych-state structureUnchanged distressed

afterAdaptation : SocialPsychState
afterAdaptation = social-psych-state structureUnchanged adapted

adaptationPreservesStructure :
  structure before ≡ structure afterAdaptation
adaptationPreservesStructure = refl

data IndividualImprovement : SocialPsychState → SocialPsychState → Set where
  canonicalIndividualImprovement : IndividualImprovement before afterAdaptation

data StructuralResolution : SocialPsychState → SocialPsychState → Set where

individualImprovementDoesNotManufactureStructuralResolution :
  IndividualImprovement before afterAdaptation →
  StructuralResolution before afterAdaptation → ⊥
individualImprovementDoesNotManufactureStructuralResolution
  canonicalIndividualImprovement ()

------------------------------------------------------------------------
-- Conversely, structural critique does not refute the admissibility of an
-- individual-level description or intervention. This prevents an inverse
-- over-promotion from the Marxist critique into a blanket anti-treatment claim.
------------------------------------------------------------------------

data IndividualInterventionAdmissible : Set where
  canonicalIndividualInterventionAdmissible : IndividualInterventionAdmissible

data StructuralCritiqueRefutesIndividualIntervention : Set where

structuralCritiqueDoesNotByItselfRefuteIndividualIntervention :
  IndividualInterventionAdmissible →
  StructuralCritiqueRefutesIndividualIntervention → ⊥
structuralCritiqueDoesNotByItselfRefuteIndividualIntervention
  canonicalIndividualInterventionAdmissible ()

------------------------------------------------------------------------
-- Typed DASHI interpretations of the four source-named contradiction classes.
-- These are intentionally non-equational: the source class motivates a formal
-- lens but is not declared definitionally identical to the DASHI theorem.
------------------------------------------------------------------------

data DashiInterpretation : LopezRiosContradictionClass → Set where
  relationalRoleNotIntrinsic :
    DashiInterpretation antiDialecticalIdealist
  actionConsumerIsSituated :
    DashiInterpretation apoliticalNeutrality
  adaptationMayPreserveStructure :
    DashiInterpretation servilityToExistingRelations
  hiddenStructuralResidualBlocksDescent :
    DashiInterpretation psychologisingMystification

canonicalAntiDialecticalInterpretation :
  DashiInterpretation antiDialecticalIdealist
canonicalAntiDialecticalInterpretation = relationalRoleNotIntrinsic

canonicalApoliticalInterpretation :
  DashiInterpretation apoliticalNeutrality
canonicalApoliticalInterpretation = actionConsumerIsSituated

canonicalServilityInterpretation :
  DashiInterpretation servilityToExistingRelations
canonicalServilityInterpretation = adaptationMayPreserveStructure

canonicalPsychologisationInterpretation :
  DashiInterpretation psychologisingMystification
canonicalPsychologisationInterpretation = hiddenStructuralResidualBlocksDescent

psychologisationRegressionRetained :
  Psych.IndividualObserverSupportsStructuralDescent → ⊥
psychologisationRegressionRetained =
  Psych.individualObserverDoesNotSupportStructuralDescent

------------------------------------------------------------------------
-- Attribution/no-promotion boundary.
------------------------------------------------------------------------

data SourceClassDefinitionallyEqualsDashiInterpretation : Set where
data LopezRiosProvedDashiAdaptationTheorem : Set where
data MarxistCritiqueImpliesAllIndividualInterventionsInvalid : Set where

sourceClassIsNotDeclaredDefinitionallyIdenticalToDashiFormalisation :
  SourceClassDefinitionallyEqualsDashiInterpretation → ⊥
sourceClassIsNotDeclaredDefinitionallyIdenticalToDashiFormalisation ()

adaptationTheoremIsRepoNativeExtension :
  LopezRiosProvedDashiAdaptationTheorem → ⊥
adaptationTheoremIsRepoNativeExtension ()

marxistCritiqueDoesNotLicenseBlanketTreatmentInvalidation :
  MarxistCritiqueImpliesAllIndividualInterventionsInvalid → ⊥
marxistCritiqueDoesNotLicenseBlanketTreatmentInvalidation ()

record LopezRiosFourContradictionsBoundary : Set where
  constructor lopez-rios-four-contradictions-boundary
  field
    fourSourceNamedClassesRetained : Bool
    sourceClassesSeparatedFromFormalTranslations : Bool
    individualImprovementCanCoexistWithStructuralInvariance : Bool
    individualImprovementAloneCertifiesStructuralResolution : Bool
    structuralCritiqueAloneInvalidatesIndividualIntervention : Bool
    exactDashiTheoremsAttributedBackToLopezRios : Bool

canonicalLopezRiosFourContradictionsBoundary :
  LopezRiosFourContradictionsBoundary
canonicalLopezRiosFourContradictionsBoundary =
  lopez-rios-four-contradictions-boundary
    true true true false false false
