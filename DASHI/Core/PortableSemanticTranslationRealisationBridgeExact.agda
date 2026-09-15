module DASHI.Core.PortableSemanticTranslationRealisationBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Core.PortableSemanticInterpretationExact as Portable
import DASHI.Core.ConsumerIndexedTranslationRealisationExact as Translation

------------------------------------------------------------------------
-- CROSS-POLLINATION WITH EXISTING TRANSLATION / REALISATION ADEQUACY
--
-- Fixing one backend turns portable interpretation into an ordinary
-- translation/realisation system.  The realised artifact retains the source
-- syntax beside the backend implementation so consumer sufficiency can state
-- the same query-indexed observation equation as SemanticRefinement.
------------------------------------------------------------------------

PortableArtifact :
  (problem : Portable.SemanticInterpretationProblem) →
  Portable.Backend problem →
  Set
PortableArtifact problem backend =
  Portable.Syntax problem × Portable.Implementation problem backend

asTranslationRealisationSystem :
  (problem : Portable.SemanticInterpretationProblem) →
  (backend : Portable.Backend problem) →
  Translation.TranslationRealisationSystem
asTranslationRealisationSystem problem backend =
  Translation.translationRealisationSystem
    (Portable.Syntax problem)
    (PortableArtifact problem backend)
    (PortableArtifact problem backend)
    (Portable.Query problem)
    (Portable.Observation problem)
    (λ syntax → syntax , Portable.interpret problem backend syntax)
    (λ representation → representation)
    (λ query artifact →
      Portable.observeImplementation problem backend query (proj₂ artifact))
    (λ _ → ⊤)
    (λ _ → ⊤)
    (λ query artifact →
      Portable.observeImplementation problem backend query (proj₂ artifact)
      ≡
      Portable.observeMeaning problem query
        (Portable.meaning problem (proj₁ artifact)))

refinementGivesAdequateFor :
  ∀ {problem backend syntax query} →
  Portable.SemanticRefinement problem backend syntax query →
  Translation.AdequateFor
    (asTranslationRealisationSystem problem backend)
    syntax
    query
refinementGivesAdequateFor receipt =
  tt , (tt , Portable.preservesObservation receipt)

record PortableSemanticTranslationRealisationBoundary : Set where
  constructor portableSemanticTranslationRealisationBoundary
  field
    backendRefinementCollapsesTranslationAndRealisationObligations : Bool
    backendRefinementCollapsesTranslationAndRealisationObligationsIsFalse :
      backendRefinementCollapsesTranslationAndRealisationObligations ≡ false
    fixedBackendMayReuseTranslationRealisationAdequacy : Bool
    fixedBackendMayReuseTranslationRealisationAdequacyIsTrue :
      fixedBackendMayReuseTranslationRealisationAdequacy ≡ true

canonicalPortableSemanticTranslationRealisationBoundary :
  PortableSemanticTranslationRealisationBoundary
canonicalPortableSemanticTranslationRealisationBoundary =
  portableSemanticTranslationRealisationBoundary
    false refl
    true refl
