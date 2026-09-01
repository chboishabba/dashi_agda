module DASHI.Cognition.PNF.ContextualFractranCatalogueQuotientExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Combinatorics.FractranComputationEquivalence as Fractran
import DASHI.Combinatorics.FractranCOL as COL

------------------------------------------------------------------------
-- Consumer-equivalent worlds may be compressed arithmetically only after an
-- explicit witness that the semantic/query equivalence implies equality of a
-- sound FRACTRAN catalogue key. Same outcome remains weaker than same world or
-- same machine trace.
------------------------------------------------------------------------

record QueryWorldCatalogueBridge
  (catalogue : Fractran.FractranCatalogue)
  : Set₁ where
  constructor queryWorldCatalogueBridge
  field
    encodeWorld : World.WorldHistory → COL.EV5
    QueryEquivalent : World.WorldHistory → World.WorldHistory → Set
    queryEquivalentImpliesSameKey :
      {left right : World.WorldHistory} →
      QueryEquivalent left right →
      Fractran.key catalogue (encodeWorld left)
      ≡ Fractran.key catalogue (encodeWorld right)

open QueryWorldCatalogueBridge public

queryEquivalentWorldsHaveSameOutcome :
  (catalogue : Fractran.FractranCatalogue) →
  (bridge : QueryWorldCatalogueBridge catalogue) →
  {left right : World.WorldHistory} →
  QueryEquivalent bridge left right →
  Fractran.SameOutcome (encodeWorld bridge left) (encodeWorld bridge right)
queryEquivalentWorldsHaveSameOutcome catalogue bridge equivalent =
  Fractran.key-complete-for-outcome catalogue
    (queryEquivalentImpliesSameKey bridge equivalent)

record CatalogueQuotientBoundary : Set where
  constructor catalogueQuotientBoundary
  field
    queryEquivalenceAutomaticallyImpliesSameCatalogueKey : Bool
    sameCatalogueKeyImpliesSameTerminalOutcome : Bool
    sameTerminalOutcomeImpliesSameSemanticWorld : Bool
    sameTerminalOutcomeImpliesSameFractranTrace : Bool

canonicalCatalogueQuotientBoundary : CatalogueQuotientBoundary
canonicalCatalogueQuotientBoundary =
  catalogueQuotientBoundary false true false false
