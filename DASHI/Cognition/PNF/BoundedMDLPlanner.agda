module DASHI.Cognition.PNF.BoundedMDLPlanner where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Cost model for a fixed semantic window W and beam width B.
--
-- The theorem is about candidate-state construction. It becomes a runtime
-- theorem only when each candidate stores a constant-size backpointer rather
-- than a copied segmentation prefix.
------------------------------------------------------------------------

evaluationCapacity : Nat → Nat → Nat → Nat
evaluationCapacity zero window beam = zero
evaluationCapacity (suc n) window beam =
  (window *ᶜ beam) +ᶜ evaluationCapacity n window beam

evaluationCapacityClosed : ∀ n window beam →
  evaluationCapacity n window beam ≡ n *ᶜ (window *ᶜ beam)
evaluationCapacityClosed zero window beam = refl
evaluationCapacityClosed (suc n) window beam
  rewrite evaluationCapacityClosed n window beam = refl

backpointerCellCapacity : Nat → Nat → Nat
backpointerCellCapacity zero beam = zero
backpointerCellCapacity (suc n) beam =
  beam +ᶜ backpointerCellCapacity n beam

backpointerCellCapacityClosed : ∀ n beam →
  backpointerCellCapacity n beam ≡ n *ᶜ beam
backpointerCellCapacityClosed zero beam = refl
backpointerCellCapacityClosed (suc n) beam
  rewrite backpointerCellCapacityClosed n beam = refl

------------------------------------------------------------------------
-- Diagnostic model for copied predecessor paths.
-- Each new endpoint retains payload proportional to the current path length.
-- This is intentionally not accepted by the linear-memory certificate.
------------------------------------------------------------------------

copiedPathPayload : Nat → Nat → Nat
copiedPathPayload zero beam = zero
copiedPathPayload (suc n) beam =
  (beam *ᶜ suc n) +ᶜ copiedPathPayload n beam

copiedPathPayloadStep : ∀ n beam →
  copiedPathPayload (suc n) beam ≡
    (beam *ᶜ suc n) +ᶜ copiedPathPayload n beam
copiedPathPayloadStep n beam = refl

data PathStorage : Set where
  copiedFullPaths constantBackpointers : PathStorage

record BackpointerState : Set where
  constructor backpointerState
  field
    accumulatedCost : Nat
    predecessorEndpoint : Nat
    segmentStart segmentEnd : Nat

open BackpointerState public

record PlannerComplexityCertificate
    (regions window beam : Nat) : Set where
  constructor plannerComplexityCertificate
  field
    pathStorage : PathStorage
    pathStorageIsConstantBackpointer :
      pathStorage ≡ constantBackpointers
    candidateEvaluationBound : Nat
    candidateEvaluationBoundIsNWB :
      candidateEvaluationBound ≡ regions *ᶜ (window *ᶜ beam)
    retainedStateBound : Nat
    retainedStateBoundIsNB :
      retainedStateBound ≡ regions *ᶜ beam

open PlannerComplexityCertificate public

canonicalPlannerComplexityCertificate : ∀ regions window beam →
  PlannerComplexityCertificate regions window beam
canonicalPlannerComplexityCertificate regions window beam =
  plannerComplexityCertificate
    constantBackpointers
    refl
    (regions *ᶜ (window *ᶜ beam))
    refl
    (regions *ᶜ beam)
    refl

copiedPathsAreNotBackpointers : copiedFullPaths ≡ constantBackpointers → ⊥
copiedPathsAreNotBackpointers ()

record PlannerImplementationWitness
    (regions window beam : Nat) : Set where
  constructor plannerImplementationWitness
  field
    stateRepresentation : PathStorage
    complexityCertificate : PlannerComplexityCertificate regions window beam
    representationMatchesCertificate :
      stateRepresentation ≡ pathStorage complexityCertificate

open PlannerImplementationWitness public

copiedImplementationCannotUseCanonicalCertificate : ∀ regions window beam →
  copiedFullPaths ≡
    pathStorage (canonicalPlannerComplexityCertificate regions window beam) → ⊥
copiedImplementationCannotUseCanonicalCertificate regions window beam proof =
  copiedPathsAreNotBackpointers proof
