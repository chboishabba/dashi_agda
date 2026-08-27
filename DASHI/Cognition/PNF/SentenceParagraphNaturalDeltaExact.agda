module DASHI.Cognition.PNF.SentenceParagraphNaturalDeltaExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact

------------------------------------------------------------------------
-- B1 runtime specialization.
--
-- A sentence-local semantic delta is transported into a paragraph-local
-- address space.  Paragraph composition consumes only transported deltas; it
-- does not require reconstruction or rescanning of the sentence carrier.
------------------------------------------------------------------------

record SentenceParagraphDeltaArchitecture
    (SentenceAddress ParagraphAddress SentenceDelta ParagraphDelta : Set) : Set₁ where
  field
    transportAddress : SentenceAddress → ParagraphAddress
    transportDelta : SentenceDelta → ParagraphDelta
    emptyParagraphDelta : ParagraphDelta
    fuseParagraphDelta : ParagraphDelta → ParagraphDelta → ParagraphDelta

    fuseAssociative :
      (left middle right : ParagraphDelta) →
      fuseParagraphDelta (fuseParagraphDelta left middle) right
        ≡
      fuseParagraphDelta left (fuseParagraphDelta middle right)

open SentenceParagraphDeltaArchitecture public

------------------------------------------------------------------------
-- Stronger B1 naturality boundary.
--
-- Associativity at the parent is not by itself enough to license recursive
-- batching.  Transport must be a homomorphism of the source fusion operation:
-- transporting an empty delta is empty, and transporting a fused source delta
-- is exactly the same as transporting each source delta and fusing at the
-- parent.  This is the theorem shape used by the recursive B2 runtime.
------------------------------------------------------------------------

record SentenceParagraphFusionNaturality
    {SentenceAddress ParagraphAddress SentenceDelta ParagraphDelta : Set}
    (architecture :
      SentenceParagraphDeltaArchitecture
        SentenceAddress ParagraphAddress SentenceDelta ParagraphDelta) : Set₁ where
  field
    emptySentenceDelta : SentenceDelta
    fuseSentenceDelta : SentenceDelta → SentenceDelta → SentenceDelta

    sourceFuseAssociative :
      (left middle right : SentenceDelta) →
      fuseSentenceDelta (fuseSentenceDelta left middle) right
        ≡
      fuseSentenceDelta left (fuseSentenceDelta middle right)

    transportEmpty :
      transportDelta architecture emptySentenceDelta
        ≡
      emptyParagraphDelta architecture

    transportFusion :
      (left right : SentenceDelta) →
      transportDelta architecture (fuseSentenceDelta left right)
        ≡
      fuseParagraphDelta architecture
        (transportDelta architecture left)
        (transportDelta architecture right)

open SentenceParagraphFusionNaturality public

------------------------------------------------------------------------
-- Work receipt: sentence->paragraph work is charged to emitted delta members.
-- There is no sentence-interior rescan term in the admitted B1 path.
------------------------------------------------------------------------

record SentenceParagraphDeltaWorkReceipt : Set where
  constructor sentenceParagraphDeltaWorkReceipt
  field
    sentenceDeltaCount : Nat
    transportedObjectCount : Nat
    transportedFactorCount : Nat
    transportedResidualCount : Nat
    paragraphFusionInputCount : Nat
    sourceInteriorRescanCount : Nat
    noSourceInteriorRescan : sourceInteriorRescanCount ≡ zero

open SentenceParagraphDeltaWorkReceipt public

------------------------------------------------------------------------
-- Reuse the existing hyperfabric naturality boundary rather than introducing
-- another theorem vocabulary.  Restriction/higher-fibre transport does not
-- inherently require reconstruction of the lower carrier.
------------------------------------------------------------------------

sentenceParagraphTransportDoesNotRequireLowerRebuild :
  RestrictionRequiresReconstructionOfVertexCarrier → ⊥
sentenceParagraphTransportDoesNotRequireLowerRebuild witness =
  restrictionCanTransportDeltaWithoutRebuild witness {A = ⊥}

------------------------------------------------------------------------
-- Negative boundaries.
------------------------------------------------------------------------

data ParagraphTransportRequiresDurableTokenIds : Set where

data ParagraphFusionRequiresSentenceInteriorRescan : Set where

data AssociativeFusionCreatesIndependentSemanticAuthority : Set where

paragraphTransportNeedNotRequireDurableTokenIds :
  ParagraphTransportRequiresDurableTokenIds → ⊥
paragraphTransportNeedNotRequireDurableTokenIds ()

paragraphFusionNeedNotRescanSentenceInterior :
  ParagraphFusionRequiresSentenceInteriorRescan → ⊥
paragraphFusionNeedNotRescanSentenceInterior ()

associativeFusionDoesNotCreateSecondAuthority :
  AssociativeFusionCreatesIndependentSemanticAuthority → ⊥
associativeFusionDoesNotCreateSecondAuthority ()
