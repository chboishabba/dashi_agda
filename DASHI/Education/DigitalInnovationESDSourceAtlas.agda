module DASHI.Education.DigitalInnovationESDSourceAtlas where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE-BOUNDED EDITORIAL CALL
--
-- This page specifies a Special Issue agenda.  It identifies questions,
-- candidate intervention families and desired evidence dimensions.  It is not
-- an empirical study and supplies no intervention-effect estimate.
------------------------------------------------------------------------

mdpiDigitalInnovationESDCall : Source.AttributedSource
mdpiDigitalInnovationESDCall =
  Source.mkNoDOISource
    "Chrysanthi Kadji-Beltran and Nikleia Eteokleous (Guest Editors)"
    "Digital Innovation for Transformative Education and Sustainable Development"
    "Sustainability, Sustainable Education and Approaches special issue"
    "2026"
    "https://www.mdpi.com/journal/sustainability/special_issues/W6I7Z68592"
    (Source.namedSourceKind "journal special-issue editorial call")
    "Defines a research agenda joining digital transformation and Education for Sustainable Development; it does not report intervention effectiveness."
    Source.publicAttribution

canonicalDigitalInnovationESDSourceAtlas : Source.AttributedSourceAtlas
canonicalDigitalInnovationESDSourceAtlas =
  Source.mkSourceAtlas
    "digital innovation / transformative education / ESD editorial-call atlas"
    "DASHI.Education.DigitalInnovationESDSourceAtlas"
    (mdpiDigitalInnovationESDCall ∷ [])
    "Source-bounded metadata and research-agenda role for the MDPI Special Issue call; manuscript deadline recorded by the source as 30 August 2027."

data EditorialCallSuppliesEffectivenessEvidencePermission : Set where

editorialCallDoesNotSupplyEffectivenessEvidence :
  EditorialCallSuppliesEffectivenessEvidencePermission → ⊥
editorialCallDoesNotSupplyEffectivenessEvidence ()

data EditorialCallPromotesAgendaToConclusionPermission : Set where

editorialCallCannotPromoteAgendaToConclusion :
  EditorialCallPromotesAgendaToConclusionPermission → ⊥
editorialCallCannotPromoteAgendaToConclusion ()

record EditorialCallBoundary : Set where
  constructor editorialCallBoundary
  field
    identifiesResearchQuestions : Bool
    identifiesResearchQuestionsIsTrue : identifiesResearchQuestions ≡ true
    identifiesDesiredEvidenceDimensions : Bool
    identifiesDesiredEvidenceDimensionsIsTrue :
      identifiesDesiredEvidenceDimensions ≡ true
    provesListedTechnologyEffective : Bool
    provesListedTechnologyEffectiveIsFalse :
      provesListedTechnologyEffective ≡ false
    provesScalability : Bool
    provesScalabilityIsFalse : provesScalability ≡ false
    provesLongTermSustainabilityImpact : Bool
    provesLongTermSustainabilityImpactIsFalse :
      provesLongTermSustainabilityImpact ≡ false
    mayPromoteResearchAgendaToAcceptedConclusion : Bool
    mayPromoteResearchAgendaToAcceptedConclusionIsFalse :
      mayPromoteResearchAgendaToAcceptedConclusion ≡ false

canonicalEditorialCallBoundary : EditorialCallBoundary
canonicalEditorialCallBoundary =
  editorialCallBoundary
    true refl true refl false refl false refl false refl false refl
