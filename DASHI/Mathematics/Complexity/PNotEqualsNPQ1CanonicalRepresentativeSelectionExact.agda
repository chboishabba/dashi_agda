module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalRepresentativeSelectionExact where

------------------------------------------------------------------------
-- CANONICAL NUMERIC ID -> REAL ROOT-REACHABLE REPRESENTATIVE
--
-- An index in a deduplicated finite key list is not an abstract quotient
-- class with a postulated representative. It is the index of a literal key
-- originating from the actual root-generated restriction-node list.
--
-- This file proves the missing PROVENANCE theorem constructively:
--
--   canonical key membership
--     -> original raw-key membership
--     -> actual restriction node + raw list membership.
--
-- No equality of proof-relevant restriction histories is assumed. Canonical
-- keys quotient only the future Boolean function at the same arity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Fin.Base as Fin
import Data.List.Base
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable

------------------------------------------------------------------------
-- Any key returned by insertion is either the new key or an existing key.
------------------------------------------------------------------------

insertKeyHasSource :
  ∀ {remaining : Nat}
    (inserted : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining))
    {query : Merge.SemanticKey remaining} →
  Merge.ListedKey query (Merge.insertSemanticKey inserted keys) →
  (query ≡ inserted) ⊎ Merge.ListedKey query keys
insertKeyHasSource inserted [] Merge.firstKey =
  inj₁ refl
insertKeyHasSource inserted (head ∷ rest) member
    with Merge.decideTableEqual inserted head
... | inj₁ same with member
...   | Merge.firstKey = inj₁ (sym same)
...   | Merge.laterKey inRest =
  inj₂ (Merge.laterKey inRest)
... | inj₂ different with member
...   | Merge.firstKey =
  inj₂ Merge.firstKey
...   | Merge.laterKey inInserted
    with insertKeyHasSource inserted rest inInserted
...     | inj₁ matches = inj₁ matches
...     | inj₂ old = inj₂ (Merge.laterKey old)

------------------------------------------------------------------------
-- Deduplication cannot invent a new semantic key.
------------------------------------------------------------------------

canonicalKeyHasRawSource :
  ∀ {remaining : Nat}
    (keys : List (Merge.SemanticKey remaining))
    {query : Merge.SemanticKey remaining} →
  Merge.ListedKey query (Merge.canonicalKeyList keys) →
  Merge.ListedKey query keys
canonicalKeyHasRawSource [] ()
canonicalKeyHasRawSource (head ∷ rest) member
    with insertKeyHasSource head (Merge.canonicalKeyList rest) member
... | inj₁ refl =
  Merge.firstKey
... | inj₂ inTail =
  Merge.laterKey (canonicalKeyHasRawSource rest inTail)

------------------------------------------------------------------------
-- A raw semantic key came from an ACTUAL node in the raw Shannon layer.
------------------------------------------------------------------------

rawKeyHasNode :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (nodes : List (Width.LayerNode {root = root} remaining))
    {key : Merge.SemanticKey remaining} →
  Merge.ListedKey key (Merge.keyForLayer nodes) →
  Σ
    (Width.LayerNode {root = root} remaining)
    (λ node →
      (Step.Listed node nodes)
      × (Merge.semanticKey node ≡ key))
rawKeyHasNode (node ∷ rest) Merge.firstKey =
  node , (Step.first , refl)
rawKeyHasNode (head ∷ rest) (Merge.laterKey inRest)
    with rawKeyHasNode rest inRest
... | node , (member , exact) =
  node , (Step.later member , exact)

------------------------------------------------------------------------
-- Every literal Fin index selects an actual member of its finite key list.
------------------------------------------------------------------------

indexLookupListed :
  ∀ {remaining : Nat}
    (keys : List (Merge.SemanticKey remaining))
    (index : Fin.Fin (Data.List.Base.length keys)) →
  Merge.ListedKey
    (Reachable.lookupKey keys index)
    keys
indexLookupListed (head ∷ tail) Fin.zero =
  Merge.firstKey
indexLookupListed (head ∷ tail) (Fin.suc index) =
  Merge.laterKey (indexLookupListed tail index)

------------------------------------------------------------------------
-- Named representative carrier and computational construction.
------------------------------------------------------------------------

record NumericRepresentative
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (index : Reachable.ReachableNumericState path) : Set₁ where
  constructor numeric-representative
  field
    node : Width.LayerNode {root = root} remaining
    inRootedLayer : Step.Listed node (Root.rootedLayer path)
    keyMatchesIndex :
      Merge.semanticKey node
      ≡ Reachable.decodeReachableState path index

open NumericRepresentative public

representativeOfIndex :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (index : Reachable.ReachableNumericState path) →
  NumericRepresentative path index
representativeOfIndex path index
    with rawKeyHasNode
      (Root.rootedLayer path)
      (canonicalKeyHasRawSource
        (Merge.keyForLayer (Root.rootedLayer path))
        (indexLookupListed
          (Root.rootedMergedSemanticKeys path)
          index))
... | actualNode , (listed , keyExact) =
  numeric-representative
    actualNode
    listed
    keyExact

------------------------------------------------------------------------
-- This provides enough data to compute a Shannon transition from ONLY the
-- arity-tagged numeric state. The next owner uses this representative with the
-- real executable key scanner and charges its search work separately.
------------------------------------------------------------------------
