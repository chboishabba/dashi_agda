module DASHI.Core.SymbolIdentityEvolutionExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- SYMBOL IDENTITY ACROSS REFACTORING
--
-- Renderer continuity may use evidence that an old symbol and a new symbol
-- represent the same evolving construction.  Evidence strength is explicit;
-- ambiguous heuristic similarity is never promoted into semantic identity.
------------------------------------------------------------------------

data IdentityEvidenceKind : Set where
  exactSemanticKey : IdentityEvidenceKind
  sourceMoveEvidence : IdentityEvidenceKind
  uniqueStructuralFingerprint : IdentityEvidenceKind
  heuristicSimilarity : IdentityEvidenceKind

data IdentityConfidence : Set where
  exactIdentity : IdentityConfidence
  supportedIdentity : IdentityConfidence
  heuristicIdentity : IdentityConfidence

record SymbolIdentityEvidence : Set where
  constructor symbolIdentityEvidence
  field
    oldSymbolId : String
    newSymbolId : String
    identityEvidenceKind : IdentityEvidenceKind
    identityConfidence : IdentityConfidence

open SymbolIdentityEvidence public

data IdentityVisualPrimitive : Set where
  preserveNode : String → IdentityVisualPrimitive
  morphNodeIdentity : String → String → IdentityVisualPrimitive
  replaceUncertainNode : String → String → IdentityVisualPrimitive

identityVisualPrimitive :
  SymbolIdentityEvidence →
  IdentityVisualPrimitive
identityVisualPrimitive
  (symbolIdentityEvidence old new exactSemanticKey exactIdentity) =
  preserveNode old
identityVisualPrimitive
  (symbolIdentityEvidence old new sourceMoveEvidence supportedIdentity) =
  morphNodeIdentity old new
identityVisualPrimitive
  (symbolIdentityEvidence old new uniqueStructuralFingerprint supportedIdentity) =
  morphNodeIdentity old new
identityVisualPrimitive
  (symbolIdentityEvidence old new heuristicSimilarity heuristicIdentity) =
  replaceUncertainNode old new

data IdentityVisualIntent : Set where
  stableIdentity : IdentityVisualIntent
  supportedMorph : IdentityVisualIntent
  uncertainReplacement : IdentityVisualIntent

identityVisualIntent : IdentityVisualPrimitive → IdentityVisualIntent
identityVisualIntent (preserveNode _) = stableIdentity
identityVisualIntent (morphNodeIdentity _ _) = supportedMorph
identityVisualIntent (replaceUncertainNode _ _) = uncertainReplacement

canonicalStructuralMorphIntent :
  ∀ old new →
  identityVisualIntent
    (identityVisualPrimitive
      (symbolIdentityEvidence
        old new
        uniqueStructuralFingerprint
        supportedIdentity))
  ≡ supportedMorph
canonicalStructuralMorphIntent _ _ = refl

record SymbolIdentityEvolutionBoundary : Set where
  constructor symbolIdentityEvolutionBoundary
  field
    heuristicSimilarityDefinesSemanticIdentity : Bool
    heuristicSimilarityDefinesSemanticIdentityIsFalse :
      heuristicSimilarityDefinesSemanticIdentity ≡ false

    uniqueStructuralEvidenceMayGuideVisualMorph : Bool
    uniqueStructuralEvidenceMayGuideVisualMorphIsTrue :
      uniqueStructuralEvidenceMayGuideVisualMorph ≡ true

    visualMorphRewritesHistoricalSource : Bool
    visualMorphRewritesHistoricalSourceIsFalse :
      visualMorphRewritesHistoricalSource ≡ false

canonicalSymbolIdentityEvolutionBoundary :
  SymbolIdentityEvolutionBoundary
canonicalSymbolIdentityEvolutionBoundary =
  symbolIdentityEvolutionBoundary
    false refl
    true refl
    false refl
