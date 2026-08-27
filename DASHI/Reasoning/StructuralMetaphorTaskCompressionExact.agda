module DASHI.Reasoning.StructuralMetaphorTaskCompressionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.MetaphorAlignmentMisunderstanding as Metaphor
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources

------------------------------------------------------------------------
-- STRUCTURAL METAPHOR AS TASK-RELATIVE COMPRESSION
--
-- The core distinction is:
--
--   rich source state -> compressed representation -> task output
--
-- A compression is sufficient only relative to a declared consumer/task when
-- the task factors through that representation.  This permits a metaphor to
-- compress a rich relational source while preserving the distinctions needed
-- for one task, without claiming losslessness for every possible consumer.
--
-- This extends the repo's existing metaphor alignment machinery rather than
-- replacing it.  MetaphorAlignmentMisunderstanding owns partial alignment and
-- audience/context receipts; this file owns task-relative factorisation.
------------------------------------------------------------------------

record TaskRelativeStructuralCompression
    (Fine Representation Task Output : Set)
    (encode : Fine → Representation)
    (evaluate : Task → Fine → Output) : Set₁ where
  constructor taskRelativeStructuralCompression
  field
    evaluateCompressed : Task → Representation → Output
    factorisesForDeclaredTask :
      (task : Task) →
      (fine : Fine) →
      evaluate task fine ≡ evaluateCompressed task (encode fine)
    compressionReading : String

open TaskRelativeStructuralCompression public

sameRepresentationSameDeclaredTaskOutput :
  ∀ {Fine Representation Task Output : Set}
    {encode : Fine → Representation}
    {evaluate : Task → Fine → Output} →
  TaskRelativeStructuralCompression Fine Representation Task Output encode evaluate →
  (task : Task) →
  {left right : Fine} →
  encode left ≡ encode right →
  evaluate task left ≡ evaluate task right
sameRepresentationSameDeclaredTaskOutput compression task same =
  trans
    (factorisesForDeclaredTask compression task _)
    (trans
      (cong (evaluateCompressed compression task) same)
      (sym (factorisesForDeclaredTask compression task _)))
  where
    open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Consumer failure is the dual condition: one coarse representation may be
-- fine for one task while losing distinctions needed by another.
------------------------------------------------------------------------

record CompressionFailureWitness
    {Fine Representation Output : Set}
    (encode : Fine → Representation)
    (consumer : Fine → Output) : Set where
  constructor compressionFailureWitness
  field
    leftFine rightFine : Fine
    sameCompressedRepresentation : encode leftFine ≡ encode rightFine
    consumerOutputsDiffer : consumer leftFine ≡ consumer rightFine → ⊥

open CompressionFailureWitness public

compressionFailureBlocksDescent :
  ∀ {Fine Representation Output : Set}
    {encode : Fine → Representation}
    {consumer : Fine → Output} →
  CompressionFailureWitness encode consumer →
  NonFactor.FactorsThrough encode consumer →
  ⊥
compressionFailureBlocksDescent witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (leftFine witness)
      (rightFine witness)
      (sameCompressedRepresentation witness)
      (consumerOutputsDiffer witness))

------------------------------------------------------------------------
-- Exact finite specimen.
--
-- A binary slogan collapses two relational situations.  A structural code
-- distinguishes them and is sufficient for the declared relational task.
------------------------------------------------------------------------

data FineRelationalState : Set where
  distinctButReciprocal distinctAndIndependent : FineRelationalState

data BinarySlogan : Set where
  merelyDifferent : BinarySlogan

data StructuralCode : Set where
  heldRelationCode independentCode : StructuralCode

data RelationalQuestion : Set where
  relationQuestion : RelationalQuestion

data RelationalAnswer : Set where
  relationRetained relationAbsent : RelationalAnswer

binarySlogan : FineRelationalState → BinarySlogan
binarySlogan _ = merelyDifferent

structuralCode : FineRelationalState → StructuralCode
structuralCode distinctButReciprocal = heldRelationCode
structuralCode distinctAndIndependent = independentCode

answerRelationalQuestion : RelationalQuestion → FineRelationalState → RelationalAnswer
answerRelationalQuestion relationQuestion distinctButReciprocal = relationRetained
answerRelationalQuestion relationQuestion distinctAndIndependent = relationAbsent

answerFromStructuralCode : RelationalQuestion → StructuralCode → RelationalAnswer
answerFromStructuralCode relationQuestion heldRelationCode = relationRetained
answerFromStructuralCode relationQuestion independentCode = relationAbsent

structuralCodeIsTaskSufficient :
  TaskRelativeStructuralCompression
    FineRelationalState StructuralCode RelationalQuestion RelationalAnswer
    structuralCode answerRelationalQuestion
structuralCodeIsTaskSufficient =
  taskRelativeStructuralCompression
    answerFromStructuralCode
    (λ
      { relationQuestion distinctButReciprocal → refl
      ; relationQuestion distinctAndIndependent → refl
      })
    "The compressed structural representation preserves exactly the distinction required by the declared relational question; no universal losslessness claim is made."

binarySloganFailure :
  CompressionFailureWitness binarySlogan (answerRelationalQuestion relationQuestion)
binarySloganFailure =
  compressionFailureWitness
    distinctButReciprocal
    distinctAndIndependent
    refl
    (λ ())

binarySloganCannotAnswerRelationalQuestion :
  NonFactor.FactorsThrough binarySlogan (answerRelationalQuestion relationQuestion) → ⊥
binarySloganCannotAnswerRelationalQuestion =
  compressionFailureBlocksDescent binarySloganFailure

------------------------------------------------------------------------
-- Bridge to existing metaphor alignment vocabulary.
------------------------------------------------------------------------

existingMetaphorOwnerRecognised : String
existingMetaphorOwnerRecognised =
  "DASHI.Reasoning.MetaphorAlignmentMisunderstanding remains the owner for partial operator-equivalence alignment and audience-relative succinctness."

metaphorSourceBoundary : Sources.StructuralMetaphorAttributionBoundary
metaphorSourceBoundary = Sources.canonicalStructuralMetaphorAttributionBoundary

record StructuralMetaphorCompressionBoundary : Set where
  constructor structuralMetaphorCompressionBoundary
  field
    taskSufficientMeansUniversallyLossless : Bool
    taskSufficientMeansUniversallyLosslessIsFalse :
      taskSufficientMeansUniversallyLossless ≡ false

    metaphoricalMeansArbitrary : Bool
    metaphoricalMeansArbitraryIsFalse :
      metaphoricalMeansArbitrary ≡ false

    metaphoricalMeansAlreadyLiteralMathematics : Bool
    metaphoricalMeansAlreadyLiteralMathematicsIsFalse :
      metaphoricalMeansAlreadyLiteralMathematics ≡ false

    structuralCompressionCanPreserveDeclaredConsumer : Bool
    structuralCompressionCanPreserveDeclaredConsumerIsTrue :
      structuralCompressionCanPreserveDeclaredConsumer ≡ true

canonicalStructuralMetaphorCompressionBoundary :
  StructuralMetaphorCompressionBoundary
canonicalStructuralMetaphorCompressionBoundary =
  structuralMetaphorCompressionBoundary
    false refl
    false refl
    false refl
    true refl
