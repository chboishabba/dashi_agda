module DASHI.Cognition.PlatoCaveSourceAttributionExact where

------------------------------------------------------------------------
-- PLATO CAVE SOURCE ATTRIBUTION
--
-- External conceptual source:
--   Plato, Republic, Book VII, 514a-520a (Stephanus pagination).
--
-- This owner attributes only the cave/shadow allegory used as a conceptual
-- metaphor.  The DASHI projection, FactorsThrough, observer-refinement,
-- causal-cone, memory-learning and resource-budget theorems are repository
-- constructions and are NOT attributed to Plato.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

platoRepublicCaveSource : Source.AttributedSource
platoRepublicCaveSource =
  Source.mkNoDOISource
    "Plato"
    "Republic, Book VII: Allegory of the Cave"
    "classical philosophical source; Stephanus 514a-520a"
    "c. fourth century BCE"
    "urn:plato:republic:book7:514a-520a"
    (Source.namedSourceKind "classical philosophical source")
    "conceptual provenance for the cave/shadow metaphor only; no DASHI projection or observer theorem is attributed to Plato"
    Source.publicAttribution

data PlatoCaveImportsDASHITheoremAuthority : Set where

platoCaveSourceDoesNotImportDASHITheoremAuthority :
  PlatoCaveImportsDASHITheoremAuthority → ⊥
platoCaveSourceDoesNotImportDASHITheoremAuthority ()
