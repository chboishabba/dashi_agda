module DASHI.Cognition.PNF.SemanticQueryFractranCatalogueBridgeExact where

-- Semantic query equivalence is not automatically FRACTRAN computation
-- equivalence.  This owner connects the two only through the repository's
-- existing FractranCatalogue soundness interface.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Combinatorics.FractranComputationEquivalence as FE
open import DASHI.Combinatorics.FractranCOL using (EV5)

------------------------------------------------------------------------
-- 1. Any source world encoded into EV5 inherits a safe catalogue key from an
--    existing proved FRACTRAN catalogue.
------------------------------------------------------------------------

semanticCatalogueKey :
  {World : Set} →
  (C : FE.FractranCatalogue) →
  (encodeWorld : World → EV5) →
  World → FE.Key C
semanticCatalogueKey C encodeWorld world = FE.key C (encodeWorld world)

semanticCatalogueKeySound :
  {World : Set} →
  (C : FE.FractranCatalogue) →
  (encodeWorld : World → EV5) →
  {x y : World} →
  semanticCatalogueKey C encodeWorld x ≡
  semanticCatalogueKey C encodeWorld y →
  FE.SameOutcome (encodeWorld x) (encodeWorld y)
semanticCatalogueKeySound C encodeWorld keyEq =
  FE.key-complete-for-outcome C keyEq

------------------------------------------------------------------------
-- 2. A semantic query may drive catalogue compression only when query
--    equivalence is proved to imply equality of the catalogue key.
------------------------------------------------------------------------

record QueryCatalogueCompatibility : Set₁ where
  constructor queryCatalogueCompatibility
  field
    World Query Observation : Set
    catalogue : FE.FractranCatalogue
    encodeWorld : World → EV5
    observe : Query → World → Observation

    queryEquivalent : Query → World → World → Set
    queryEquivalentSound :
      (q : Query) (x y : World) →
      queryEquivalent q x y →
      observe q x ≡ observe q y

    queryEquivalentImpliesCatalogueKeyEqual :
      (q : Query) (x y : World) →
      queryEquivalent q x y →
      semanticCatalogueKey catalogue encodeWorld x ≡
      semanticCatalogueKey catalogue encodeWorld y

open QueryCatalogueCompatibility public

queryEquivalentWorldsHaveSameFractranOutcome :
  (B : QueryCatalogueCompatibility) →
  (q : Query B) →
  (x y : World B) →
  queryEquivalent B q x y →
  FE.SameOutcome (encodeWorld B x) (encodeWorld B y)
queryEquivalentWorldsHaveSameFractranOutcome B q x y eq =
  semanticCatalogueKeySound
    (catalogue B)
    (encodeWorld B)
    (queryEquivalentImpliesCatalogueKeyEqual B q x y eq)

------------------------------------------------------------------------
-- 3. The converse is deliberately not assumed.
--
-- Same terminal FRACTRAN outcome is weaker than semantic/world equality and
-- weaker than identical execution trace, exactly as the existing FRACTRAN
-- computation-equivalence owner records.
------------------------------------------------------------------------

record SemanticFractranCompressionBoundary : Set where
  constructor semanticFractranCompressionBoundary
  field
    queryEquivalenceAloneAuthorisesCompression : Bool
    queryEquivalenceAloneAuthorisesCompressionIsFalse :
      queryEquivalenceAloneAuthorisesCompression ≡ false

    catalogueKeyWitnessAuthorisesOutcomeCompression : Bool
    catalogueKeyWitnessAuthorisesOutcomeCompressionIsTrue :
      catalogueKeyWitnessAuthorisesOutcomeCompression ≡ true

    sameFractranOutcomeImpliesSameSemanticWorld : Bool
    sameFractranOutcomeImpliesSameSemanticWorldIsFalse :
      sameFractranOutcomeImpliesSameSemanticWorld ≡ false

    sameFractranOutcomeImpliesSameTrace : Bool
    sameFractranOutcomeImpliesSameTraceIsFalse :
      sameFractranOutcomeImpliesSameTrace ≡ false

canonicalSemanticFractranCompressionBoundary :
  SemanticFractranCompressionBoundary
canonicalSemanticFractranCompressionBoundary =
  semanticFractranCompressionBoundary
    false refl
    true refl
    false refl
    false refl
