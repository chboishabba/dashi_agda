{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.NumericStreamSemanticCompilationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NUMERIC PARSER ROWS ARE THE COMPILER INPUT CARRIER
--
-- Once parser observations have been committed to numeric token/head/annotation
-- rows, semantic factor/object/demand production may factor directly through
-- that numeric carrier.  A reconstructed rich parser graph may exist as a debug
-- or compatibility view, but it is not a semantic prerequisite.
------------------------------------------------------------------------

record NumericStreamSemanticCompilation
  (NumericBatch RichGraph Factors Objects Demands Authority : Set) : Set₁ where
  field
    factorsFromNumeric : NumericBatch → Factors
    objectsFromNumeric : NumericBatch → Objects
    demandsFromNumeric : NumericBatch → Demands
    authorityFromNumeric : NumericBatch → Authority

    reconstructRichGraph : NumericBatch → RichGraph
    authorityFromRichGraph : RichGraph → Authority

    numericAuthorityExact :
      (batch : NumericBatch) →
      authorityFromNumeric batch
        ≡ authorityFromRichGraph (reconstructRichGraph batch)

open NumericStreamSemanticCompilation public

directNumericCompilationPreservesDeclaredAuthority :
  ∀ {NumericBatch RichGraph Factors Objects Demands Authority : Set}
    (compiler : NumericStreamSemanticCompilation
      NumericBatch RichGraph Factors Objects Demands Authority)
    (batch : NumericBatch) →
  authorityFromNumeric compiler batch
    ≡ authorityFromRichGraph compiler (reconstructRichGraph compiler batch)
directNumericCompilationPreservesDeclaredAuthority compiler =
  numericAuthorityExact compiler

------------------------------------------------------------------------
-- STREAM/BATCH PHYSICALIZATION
--
-- A stream may be partitioned into batches for bounded memory.  Batching is an
-- execution concern; it is admissible only with an authority equality proof.
------------------------------------------------------------------------

record ExactNumericBatching (Stream Batched Authority : Set) : Set₁ where
  field
    batch : Stream → Batched
    compileStream : Stream → Authority
    compileBatched : Batched → Authority
    batchingExact :
      (stream : Stream) →
      compileBatched (batch stream) ≡ compileStream stream

open ExactNumericBatching public

------------------------------------------------------------------------
-- Anti-confusion boundary.
------------------------------------------------------------------------

data RichGraphRequiredAfterNumericCommitPermission : Set where

data BoundedBatchingMayChangeAuthorityPermission : Set where

richGraphIsNotRequiredByNumericAuthority :
  RichGraphRequiredAfterNumericCommitPermission → ⊥
richGraphIsNotRequiredByNumericAuthority ()

boundedBatchingCannotChangeAuthorityWithoutNewSemantics :
  BoundedBatchingMayChangeAuthorityPermission → ⊥
boundedBatchingCannotChangeAuthorityWithoutNewSemantics ()
