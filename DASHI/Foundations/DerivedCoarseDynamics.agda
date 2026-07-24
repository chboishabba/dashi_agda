module DASHI.Foundations.DerivedCoarseDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record DeterministicCoarseQuotient (Fine Coarse : Set) : Set₁ where
  field
    project : Fine → Coarse
    fineStep : Fine → Fine
    coarseStep : Coarse → Coarse
    commutes : ∀ state → project (fineStep state) ≡ coarseStep (project state)

open DeterministicCoarseQuotient public

record SetValuedCoarseDynamics (Fine Coarse : Set) : Set₁ where
  field
    setProject : Fine → Coarse
    setFineStep : Fine → Fine
    Successor : Coarse → Coarse → Set
    projectedFineStepIsSuccessor :
      ∀ state → Successor (setProject state) (setProject (setFineStep state))

open SetValuedCoarseDynamics public

record TransitionKernel (Coarse Weight : Set) : Set₁ where
  field
    kernel : Coarse → Coarse → Weight
    normalisationReceipt : Set
    projectionOrSamplingReceipt : Set

open TransitionKernel public

deterministicAsSetValued :
  ∀ {Fine Coarse} →
  DeterministicCoarseQuotient Fine Coarse →
  SetValuedCoarseDynamics Fine Coarse
deterministicAsSetValued quotient =
  record
    { setProject = DeterministicCoarseQuotient.project quotient
    ; setFineStep = DeterministicCoarseQuotient.fineStep quotient
    ; Successor = λ current next →
        next ≡ DeterministicCoarseQuotient.coarseStep quotient current
    ; projectedFineStepIsSuccessor =
        DeterministicCoarseQuotient.commutes quotient
    }

data CoarseDynamicsKind : Set where
  deterministic setValued stochastic : CoarseDynamicsKind

classifyCoarseDynamics : Bool → Bool → CoarseDynamicsKind
classifyCoarseDynamics true _ = deterministic
classifyCoarseDynamics false true = setValued
classifyCoarseDynamics false false = stochastic

canonicalDeterministicClassification :
  classifyCoarseDynamics true false ≡ deterministic
canonicalDeterministicClassification = refl
