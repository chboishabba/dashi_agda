module DASHI.Culture.CohnTechnostrategicSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- CAROL COHN / TECHNOSTRATEGIC DISCOURSE SOURCE ATLAS
--
-- Source identity is kept separate from DASHI theorem ownership.  Cohn's
-- publications motivate bounded discourse/abstraction questions; they do not
-- author DASHI's finite collisions, factorisation obstructions, observer
-- refinements, or naturalisation countermodels.
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

------------------------------------------------------------------------
-- Snowball child: the 1993 chapter remains a distinct source object.
--
-- It can extend the bounded gender/war-language source surface without being
-- collapsed into the 1987 article, and without being treated as authorship of
-- the repository's expression/admissibility/reality theorem.
------------------------------------------------------------------------

cohnWarsWimpsWomen : Source.AttributedSource
cohnWarsWimpsWomen =
  Source.mkDOISource
    "Carol Cohn"
    "Wars, Wimps, and Women: Talking Gender and Thinking War"
    "Gendering War Talk, ed. Miriam Cooke and Angela Woollacott, Princeton University Press, pp. 227-246"
    "1993"
    "10.1515/9781400863235.227"
    "https://doi.org/10.1515/9781400863235.227"
    Source.academicChapterSource
    "source-bounded continuation of Cohn's gender-and-war discourse analysis; used only to extend the attributed source genealogy and not as proof of DASHI's admissibility, naturalisation, causation, or authority theorems"
    Source.publicAttribution

cohnSexAndDeathSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt cohnSexAndDeath
cohnSexAndDeathSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt cohnSexAndDeath

cohnWarsWimpsWomenSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt cohnWarsWimpsWomen
cohnWarsWimpsWomenSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt cohnWarsWimpsWomen

cohnTechnostrategicAtlas : Source.AttributedSourceAtlas
cohnTechnostrategicAtlas =
  Source.mkSourceAtlas
    "Carol Cohn technostrategic discourse source atlas"
    "DASHI.Culture.CohnTechnostrategicSourceAtlasExact"
    (cohnSexAndDeath ∷ cohnWarsWimpsWomen ∷ [])
    "source-bounded support for the Cohn technostrategic/gender-war discourse fixture only; each source keeps its own identity, source kind and formalisation relationship; the atlas does not establish a universal causal law, endorse every later interpretation, or import feminist/Foucauldian/Lacanian authority"

cohnSourceCount :
  Source.sourceCount (Source.sources cohnTechnostrategicAtlas)
  ≡ suc (suc zero)
cohnSourceCount = refl

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
    sourceGenealogyProvesCausalContinuity : Bool
    sourceGenealogyProvesCausalContinuityIsFalse :
      sourceGenealogyProvesCausalContinuity ≡ false
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
    false refl

cohnAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority cohnTechnostrategicAtlas ≡ false
cohnAtlasDoesNotCreateAuthority = refl

cohnCitationDoesNotImportProof :
  Source.citationImportsProof cohnSexAndDeath ≡ false
cohnCitationDoesNotImportProof = refl

cohnSnowballCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority cohnWarsWimpsWomen ≡ false
cohnSnowballCitationDoesNotCreateAuthority = refl
