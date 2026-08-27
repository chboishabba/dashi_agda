module DASHI.Reasoning.ConsumerRelativeMetaphorTransferFitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources

------------------------------------------------------------------------
-- CONSUMER-RELATIVE STRUCTURAL TRANSFER FITNESS
--
-- A metaphor need not preserve every predicate or relation of either source or
-- target.  What matters here is indexed sufficiency: a representation may be
-- useful for one declared task while inducing a collision that makes it
-- insufficient for another.
--
-- This is an original DASHI formalisation.  Stuart & Wilkenfeld (2022), DOI
-- 10.1007/s13194-022-00479-5, motivate the consequence-, context-,
-- representation-, and ability-relative reading of metaphorical understanding;
-- they do not state the factorisation theorems below.
------------------------------------------------------------------------

record ConsumerRelativeTransferFitness
    (Fine Representation PrimaryTask PrimaryAnswer SecondaryAnswer : Set)
    (encode : Fine → Representation)
    (primary : PrimaryTask → Fine → PrimaryAnswer)
    (secondary : Fine → SecondaryAnswer) : Set₁ where
  constructor consumerRelativeTransferFitness
  field
    primaryCompression :
      Compression.TaskRelativeStructuralCompression
        Fine Representation PrimaryTask PrimaryAnswer
        encode primary

    secondaryFailure :
      Compression.CompressionFailureWitness encode secondary

    transferReading : String

open ConsumerRelativeTransferFitness public

primaryTaskFactorsThroughMetaphor :
  ∀ {Fine Representation PrimaryTask PrimaryAnswer SecondaryAnswer : Set}
    {encode : Fine → Representation}
    {primary : PrimaryTask → Fine → PrimaryAnswer}
    {secondary : Fine → SecondaryAnswer} →
  ConsumerRelativeTransferFitness
    Fine Representation PrimaryTask PrimaryAnswer SecondaryAnswer
    encode primary secondary →
  Compression.TaskRelativeStructuralCompression
    Fine Representation PrimaryTask PrimaryAnswer
    encode primary
primaryTaskFactorsThroughMetaphor fitness = primaryCompression fitness

secondaryConsumerCannotDescendThroughMetaphor :
  ∀ {Fine Representation PrimaryTask PrimaryAnswer SecondaryAnswer : Set}
    {encode : Fine → Representation}
    {primary : PrimaryTask → Fine → PrimaryAnswer}
    {secondary : Fine → SecondaryAnswer} →
  ConsumerRelativeTransferFitness
    Fine Representation PrimaryTask PrimaryAnswer SecondaryAnswer
    encode primary secondary →
  NonFactor.FactorsThrough encode secondary → ⊥
secondaryConsumerCannotDescendThroughMetaphor fitness =
  Compression.compressionFailureBlocksDescent
    (secondaryFailure fitness)

------------------------------------------------------------------------
-- Context-indexed goodness.
--
-- This finite surface captures the logical point:
--
--   useful here != useful everywhere.
--
-- It is deliberately weaker than a scalar universal metaphor-quality metric.
------------------------------------------------------------------------

data FitnessJudgement : Set where
  usefulForDeclaredTask insufficientForDeclaredTask : FitnessJudgement

record ContextIndexedFitness
    (Metaphor Context : Set) : Set₁ where
  field
    judge : Metaphor → Context → FitnessJudgement
    contextReading : String

open ContextIndexedFitness public

record SameMetaphorDifferentContextFitness
    {Metaphor Context : Set}
    (surface : ContextIndexedFitness Metaphor Context) : Set where
  field
    metaphor : Metaphor
    usefulContext : Context
    insufficientContext : Context
    usefulHere : judge surface metaphor usefulContext ≡ usefulForDeclaredTask
    insufficientThere :
      judge surface metaphor insufficientContext ≡ insufficientForDeclaredTask

------------------------------------------------------------------------
-- Synthetic pedagogical specimen.
--
-- Two unresolved states are identical for the coarse question 'is an outcome
-- already resolved?' but differ for the richer question 'what kind of
-- unresolved structure is present?'.  The example intentionally avoids
-- identifying this tiny carrier with quantum mechanics or any other physical
-- theory.
------------------------------------------------------------------------

data ToyFineState : Set where
  unresolvedRelational unresolvedIgnorance resolvedState : ToyFineState

data ToyMetaphorCode : Set where
  unresolvedCode resolvedCode : ToyMetaphorCode

data ToyPrimaryTask : Set where
  resolvedQuestion : ToyPrimaryTask

data ToyPrimaryAnswer : Set where
  unresolvedAnswer resolvedAnswer : ToyPrimaryAnswer

data ToySecondaryAnswer : Set where
  relationalResidual ignoranceResidual resolvedResidual : ToySecondaryAnswer

encodeToy : ToyFineState → ToyMetaphorCode
encodeToy unresolvedRelational = unresolvedCode
encodeToy unresolvedIgnorance = unresolvedCode
encodeToy resolvedState = resolvedCode

primaryToy : ToyPrimaryTask → ToyFineState → ToyPrimaryAnswer
primaryToy resolvedQuestion unresolvedRelational = unresolvedAnswer
primaryToy resolvedQuestion unresolvedIgnorance = unresolvedAnswer
primaryToy resolvedQuestion resolvedState = resolvedAnswer

decodePrimaryToy : ToyPrimaryTask → ToyMetaphorCode → ToyPrimaryAnswer
decodePrimaryToy resolvedQuestion unresolvedCode = unresolvedAnswer
decodePrimaryToy resolvedQuestion resolvedCode = resolvedAnswer

secondaryToy : ToyFineState → ToySecondaryAnswer
secondaryToy unresolvedRelational = relationalResidual
secondaryToy unresolvedIgnorance = ignoranceResidual
secondaryToy resolvedState = resolvedResidual

toyPrimaryCompression :
  Compression.TaskRelativeStructuralCompression
    ToyFineState ToyMetaphorCode ToyPrimaryTask ToyPrimaryAnswer
    encodeToy primaryToy
toyPrimaryCompression =
  Compression.taskRelativeStructuralCompression
    decodePrimaryToy
    (λ
      { resolvedQuestion unresolvedRelational → refl
      ; resolvedQuestion unresolvedIgnorance → refl
      ; resolvedQuestion resolvedState → refl
      })
    "The toy metaphor is sufficient only for the coarse resolved/unresolved question."

toySecondaryFailure :
  Compression.CompressionFailureWitness encodeToy secondaryToy
toySecondaryFailure =
  Compression.compressionFailureWitness
    unresolvedRelational
    unresolvedIgnorance
    refl
    (λ ())

toyConsumerRelativeFitness :
  ConsumerRelativeTransferFitness
    ToyFineState ToyMetaphorCode ToyPrimaryTask ToyPrimaryAnswer ToySecondaryAnswer
    encodeToy primaryToy secondaryToy
toyConsumerRelativeFitness =
  consumerRelativeTransferFitness
    toyPrimaryCompression
    toySecondaryFailure
    "One compressed representation can aid one question while erasing a distinction required by another; metaphor fitness is therefore consumer-relative rather than universal."

data ToyMetaphor : Set where
  coarseUncertaintyMetaphor : ToyMetaphor

data ToyContext : Set where
  coarsePedagogy richerStructureQuestion : ToyContext

toyContextFitness : ContextIndexedFitness ToyMetaphor ToyContext
toyContextFitness =
  record
    { judge = λ
        { coarseUncertaintyMetaphor coarsePedagogy → usefulForDeclaredTask
        ; coarseUncertaintyMetaphor richerStructureQuestion → insufficientForDeclaredTask
        }
    ; contextReading =
        "The same metaphor may be useful for a coarse pedagogical consumer and insufficient for a richer structural consumer."
    }

toyUsefulHereNotEverywhere :
  SameMetaphorDifferentContextFitness toyContextFitness
toyUsefulHereNotEverywhere =
  record
    { metaphor = coarseUncertaintyMetaphor
    ; usefulContext = coarsePedagogy
    ; insufficientContext = richerStructureQuestion
    ; usefulHere = refl
    ; insufficientThere = refl
    }

------------------------------------------------------------------------
-- Attribution / non-promotion boundary.
------------------------------------------------------------------------

stuartWilkenfeldSource : Sources.SourceReference
stuartWilkenfeldSource = Sources.stuartWilkenfeld2022

record MetaphorTransferFitnessBoundary : Set where
  constructor metaphorTransferFitnessBoundary
  field
    goodForOneTaskMeansGoodForEveryTask : Bool
    goodForOneTaskMeansGoodForEveryTaskIsFalse :
      goodForOneTaskMeansGoodForEveryTask ≡ false

    partialLiteralFalsehoodMakesMetaphorEpistemicallyUseless : Bool
    partialLiteralFalsehoodMakesMetaphorEpistemicallyUselessIsFalse :
      partialLiteralFalsehoodMakesMetaphorEpistemicallyUseless ≡ false

    taskSufficiencyMeansSourceTargetIsomorphism : Bool
    taskSufficiencyMeansSourceTargetIsomorphismIsFalse :
      taskSufficiencyMeansSourceTargetIsomorphism ≡ false

    toyCarrierIsQuantumMechanicalModel : Bool
    toyCarrierIsQuantumMechanicalModelIsFalse :
      toyCarrierIsQuantumMechanicalModel ≡ false

    dashiFactorisationIsClaimedByStuartWilkenfeld : Bool
    dashiFactorisationIsClaimedByStuartWilkenfeldIsFalse :
      dashiFactorisationIsClaimedByStuartWilkenfeld ≡ false

canonicalMetaphorTransferFitnessBoundary : MetaphorTransferFitnessBoundary
canonicalMetaphorTransferFitnessBoundary =
  metaphorTransferFitnessBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
