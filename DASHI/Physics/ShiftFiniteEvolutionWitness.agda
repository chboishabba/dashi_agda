module DASHI.Physics.ShiftFiniteEvolutionWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU
open import DASHI.Physics.ShiftWaveRefinementLevel as SWRL
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH

------------------------------------------------------------------------
-- Finite PNF / Skolem / Herbrand-style witness packaging over the current
-- multiscale wave stack.
--
-- This does not search an unbounded space. It only packages:
--   * a bounded existential evolution obligation,
--   * an explicit witness field obtained by one-pass update,
--   * a finite two-step history surface for current candidates.

data BoundedStepCount : Set where
  zeroStep oneStep twoStep : BoundedStepCount

iterateBounded :
  {A : Set} →
  BoundedStepCount →
  (A → A) →
  A →
  A
iterateBounded zeroStep step x = x
iterateBounded oneStep step x = step x
iterateBounded twoStep step x = step (step x)

record FiniteEvolutionObligation : Setω where
  field
    levelLabel : String
    Field : Set
    startField : Field
    targetField : Field
    stepBudget : BoundedStepCount
    obligation : Set
    nonClaimBoundary : List String

record SkolemEvolutionWitness
  (obligation : FiniteEvolutionObligation)
  : Setω where
  field
    witnessBudget : BoundedStepCount
    witnessField : FiniteEvolutionObligation.Field obligation
    witnessSatisfies :
      FiniteEvolutionObligation.targetField obligation ≡ witnessField

record FiniteHistory (A : Set) : Set where
  field
    initial : A
    afterOne : A
    afterTwo : A

record FiniteHerbrandSurface : Setω where
  field
    levelLabel : String
    Field : Set
    candidateHistory : Field → FiniteHistory Field
    nonClaimBoundary : List String

coarseOnePassObligation :
  SSL.ShiftWaveField → FiniteEvolutionObligation
coarseOnePassObligation ψ =
  record
    { levelLabel = "shift-wave-level-3"
    ; Field = SSL.ShiftWaveField
    ; startField = ψ
    ; targetField = SWGU.coarseGlobalUpdate ψ
    ; stepBudget = oneStep
    ; obligation =
        Σ SSL.ShiftWaveField (λ χ → SWGU.coarseGlobalUpdate ψ ≡ χ)
    ; nonClaimBoundary =
        "Finite one-pass evolution obligation only"
        ∷ "existential target is bounded by one explicit synchronous update"
        ∷ "No unbounded search or asymptotic convergence claim is implied"
        ∷ []
    }

fineOnePassObligation :
  SWRH.ShiftWaveField5 → FiniteEvolutionObligation
fineOnePassObligation ψ =
  record
    { levelLabel = "shift-wave-level-5"
    ; Field = SWRH.ShiftWaveField5
    ; startField = ψ
    ; targetField = SWGU.fineGlobalUpdate ψ
    ; stepBudget = oneStep
    ; obligation =
        Σ SWRH.ShiftWaveField5 (λ χ → SWGU.fineGlobalUpdate ψ ≡ χ)
    ; nonClaimBoundary =
        "Finite one-pass evolution obligation only"
        ∷ "existential target is bounded by one explicit synchronous update"
        ∷ "No unbounded search or asymptotic convergence claim is implied"
        ∷ []
    }

coarseOnePassWitness :
  (ψ : SSL.ShiftWaveField) →
  SkolemEvolutionWitness (coarseOnePassObligation ψ)
coarseOnePassWitness ψ =
  record
    { witnessBudget = oneStep
    ; witnessField = SWGU.coarseGlobalUpdate ψ
    ; witnessSatisfies = refl
    }

fineOnePassWitness :
  (ψ : SWRH.ShiftWaveField5) →
  SkolemEvolutionWitness (fineOnePassObligation ψ)
fineOnePassWitness ψ =
  record
    { witnessBudget = oneStep
    ; witnessField = SWGU.fineGlobalUpdate ψ
    ; witnessSatisfies = refl
    }

coarseHistory :
  SSL.ShiftWaveField →
  FiniteHistory SSL.ShiftWaveField
coarseHistory ψ =
  record
    { initial = ψ
    ; afterOne = SWGU.coarseGlobalUpdate ψ
    ; afterTwo = SWGU.coarseGlobalUpdate (SWGU.coarseGlobalUpdate ψ)
    }

fineHistory :
  SWRH.ShiftWaveField5 →
  FiniteHistory SWRH.ShiftWaveField5
fineHistory ψ =
  record
    { initial = ψ
    ; afterOne = SWGU.fineGlobalUpdate ψ
    ; afterTwo = SWGU.fineGlobalUpdate (SWGU.fineGlobalUpdate ψ)
    }

coarseHerbrandSurface : FiniteHerbrandSurface
coarseHerbrandSurface =
  record
    { levelLabel = "shift-wave-level-3"
    ; Field = SSL.ShiftWaveField
    ; candidateHistory = coarseHistory
    ; nonClaimBoundary =
        "Finite Herbrand-style history surface only"
        ∷ "candidate histories are bounded to the first two synchronous updates"
        ∷ "No exhaustive enumeration or completeness claim is implied"
        ∷ []
    }

fineHerbrandSurface : FiniteHerbrandSurface
fineHerbrandSurface =
  record
    { levelLabel = "shift-wave-level-5"
    ; Field = SWRH.ShiftWaveField5
    ; candidateHistory = fineHistory
    ; nonClaimBoundary =
        "Finite Herbrand-style history surface only"
        ∷ "candidate histories are bounded to the first two synchronous updates"
        ∷ "No exhaustive enumeration or completeness claim is implied"
        ∷ []
    }

record ShiftFiniteEvolutionWitness : Setω where
  field
    refinementFamily : SWRL.ShiftWaveRefinementFamily
    coarseObligation : SSL.ShiftWaveField → FiniteEvolutionObligation
    fineObligation : SWRH.ShiftWaveField5 → FiniteEvolutionObligation
    coarseSkolemWitness :
      (ψ : SSL.ShiftWaveField) →
      SkolemEvolutionWitness (coarseObligation ψ)
    fineSkolemWitness :
      (ψ : SWRH.ShiftWaveField5) →
      SkolemEvolutionWitness (fineObligation ψ)
    coarseHerbrand : FiniteHerbrandSurface
    fineHerbrand : FiniteHerbrandSurface
    nonClaimBoundary : List String

shiftFiniteEvolutionWitness : ShiftFiniteEvolutionWitness
shiftFiniteEvolutionWitness =
  record
    { refinementFamily = SWRL.shiftWaveRefinementFamily3to5
    ; coarseObligation = coarseOnePassObligation
    ; fineObligation = fineOnePassObligation
    ; coarseSkolemWitness = coarseOnePassWitness
    ; fineSkolemWitness = fineOnePassWitness
    ; coarseHerbrand = coarseHerbrandSurface
    ; fineHerbrand = fineHerbrandSurface
    ; nonClaimBoundary =
        "Finite evolution witness surface only"
        ∷ "PNF-style obligations are bounded existential packages over one-pass updates"
        ∷ "Skolem witnesses are explicit update fields, not hidden choice operators"
        ∷ "Herbrand histories are finite candidate traces, not exhaustive proof search"
        ∷ []
    }
