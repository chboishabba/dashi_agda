module DASHI.Codec.DNADeBruijnMacros where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Codec.DNAFirstFormalism using (Base; complement)
open import DASHI.Codec.DNAProductionConstraints using (ProductionState)
open import DASHI.Codec.DNAProductionDeBruijn using
  ( Edge; LabelledWalk )
open import DASHI.Codec.DNADeBruijnWalks using
  ( append; appendWalk )
open import DASHI.Codec.DNADeBruijnGeometry using
  ( Traversal; Transfer; serialise; sourceField; incoming; outgoing; path )

------------------------------------------------------------------------
-- Macros carry sequential boundary semantics only after serialization.

record SerializedMacro (Summary : Set) : Set₁ where
  constructor serializedMacro
  field
    word : List Base
    start : ProductionState
    finish : ProductionState
    summary : Summary
    legalPath : LabelledWalk start word finish
open SerializedMacro public

fromTransfer :
  ∀ {Shape Summary}
  (traversal : Traversal Shape) →
  (summarize : Shape → Summary) →
  Transfer Shape traversal →
  SerializedMacro Summary
fromTransfer traversal summarize block =
  serializedMacro
    (serialise traversal (sourceField block))
    (incoming block)
    (outgoing block)
    (summarize (sourceField block))
    (path block)

record CompositeSummary (Left Right : Set) : Set where
  constructor compositeSummary
  field
    leftSummary : Left
    rightSummary : Right
open CompositeSummary public

composeMacros :
  ∀ {Left Right}
  (left : SerializedMacro Left) →
  (right : SerializedMacro Right) →
  finish left ≡ start right →
  SerializedMacro (CompositeSummary Left Right)
composeMacros left right refl =
  serializedMacro
    (append (word left) (word right))
    (start left)
    (finish right)
    (compositeSummary (summary left) (summary right))
    (appendWalk (legalPath left) (legalPath right))

------------------------------------------------------------------------
-- A residual selects a source word inside a summary-and-boundary fibre.

record ResidualFibre (Summary Residual : Set) : Set₁ where
  field
    decodeResidual :
      (macro : SerializedMacro Summary) → Residual → List Base
    reconstructsInsideBoundary :
      (macro : SerializedMacro Summary) →
      (residual : Residual) →
      Σ ProductionState
        (λ t → LabelledWalk (start macro) (decodeResidual macro residual) t)

------------------------------------------------------------------------
-- Reverse complement reverses path direction. Whether the production policy
-- admits this action requires an explicit state dual and edge theorem.

record ReverseComplementGraphAction : Set₁ where
  field
    reverseState : ProductionState → ProductionState
    edgeAnti :
      ∀ {s b t} →
      Edge s b t →
      Edge (reverseState t) (complement b) (reverseState s)

-- No instance is fabricated here: the current bounded-history representation
-- is directional, and its reverse-state construction must be proved separately.
