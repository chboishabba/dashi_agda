module DASHI.Culture.CohnTechnostrategicSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CAROL COHN / TECHNOSTRATEGIC DISCOURSE SOURCE ATLAS
--
-- Source identity is kept separate from DASHI theorem ownership.  Cohn's
-- article motivates the bounded discourse/abstraction questions below; it does
-- not author DASHI's finite collision, factorisation obstruction, or enriched
-- observer repair.
------------------------------------------------------------------------

cohnSexAndDeath : Source.AttributedSource
cohnSexAndDeath =
  Source.mkDOISource
    "Carol Cohn"
    "Sex and Death in the Rational World of Defense Intellectuals"
    "Signs 12(4), 687-718"
    "1987"
    "10.1086/494362"
    "https://doi.org/10.1086/494362"
    Source.academicArticleSource
    "primary conceptual source for Cohn's analysis of technostrategic discourse, gendered/sexualised imagery, expert enculturation, abstraction, and the relation between strategic language and what becomes readily thinkable; DASHI owns the finite non-factorability and observer-refinement constructions"
    Source.publicAttribution

cohnTechnostrategicAtlas : Source.AttributedSourceAtlas
cohnTechnostrategicAtlas =
  Source.mkSourceAtlas
    "Carol Cohn technostrategic discourse source atlas"
    "DASHI.Culture.CohnTechnostrategicSourceAtlasExact"
    (cohnSexAndDeath ∷ [])
    "source-bounded support for the technostrategic discourse fixture only; the atlas does not establish a universal causal law, endorse every later interpretation, or import feminist/Foucauldian/Lacanian authority"

------------------------------------------------------------------------
-- Explicit non-promotion boundary.
------------------------------------------------------------------------

record CohnSourceBoundary : Set where
  constructor cohnSourceBoundary
  field
    citationCreatesDASHITheorem : Bool
    citationCreatesDASHITheoremIsFalse : citationCreatesDASHITheorem ≡ false
    articleProvesGenderedMetaphorCausesPolicy : Bool
    articleProvesGenderedMetaphorCausesPolicyIsFalse :
      articleProvesGenderedMetaphorCausesPolicy ≡ false
    articleMakesCohnHistoricallyFoucauldian : Bool
    articleMakesCohnHistoricallyFoucauldianIsFalse :
      articleMakesCohnHistoricallyFoucauldian ≡ false
    articleMakesCohnHistoricallyLacanian : Bool
    articleMakesCohnHistoricallyLacanianIsFalse :
      articleMakesCohnHistoricallyLacanian ≡ false
    finiteCollisionIsSourceAuthored : Bool
    finiteCollisionIsSourceAuthoredIsFalse : finiteCollisionIsSourceAuthored ≡ false

open CohnSourceBoundary public

canonicalCohnSourceBoundary : CohnSourceBoundary
canonicalCohnSourceBoundary =
  cohnSourceBoundary
    false refl
    false refl
    false refl
    false refl
    false refl

cohnAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority cohnTechnostrategicAtlas ≡ false
cohnAtlasDoesNotCreateAuthority = refl

cohnCitationDoesNotImportProof :
  Source.citationImportsProof cohnSexAndDeath ≡ false
cohnCitationDoesNotImportProof = refl
