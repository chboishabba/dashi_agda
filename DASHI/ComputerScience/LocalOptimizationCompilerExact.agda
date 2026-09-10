module DASHI.ComputerScience.LocalOptimizationCompilerExact where

-- Least-privilege optimization compiler.
--
-- The primitive payment is local: an optimized update preserves the relation
-- connecting spec and optimized states.  Whole-fold consumer equality is then
-- compiler output.  Resource accounting is intentionally separate: semantic
-- equivalence neither proves nor consumes a residency bound.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)

private
  variable
    ℓs ℓo ℓx ℓq ℓr : Level
    SpecState : Set ℓs
    OptState  : Set ℓo
    Input     : Set ℓx
    Obs       : Set ℓq

------------------------------------------------------------------------
-- Generic state folds.
------------------------------------------------------------------------

fold : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
fold step s []       = s
fold step s (x ∷ xs) = fold step (step s x) xs

record LocalSemanticCompiler
  (SpecState : Set ℓs)
  (OptState  : Set ℓo)
  (Input     : Set ℓx)
  (Obs       : Set ℓq)
  : Set (ℓs ⊔ ℓo ⊔ ℓx ⊔ ℓq) where
  field
    specStep : SpecState → Input → SpecState
    optStep  : OptState → Input → OptState
    Related  : SpecState → OptState → Set ℓr
    observeSpec : SpecState → Obs
    observeOpt  : OptState → Obs

    -- Small primitive payment: one local input preserves the cross-
    -- implementation relation.
    localLaw : ∀ {s o} (x : Input) → Related s o → Related (specStep s x) (optStep o x)

    -- The consumer sees only this projection; full internal-state equality is
    -- deliberately not required.
    consumerLaw : ∀ {s o} → Related s o → observeSpec s ≡ observeOpt o

open LocalSemanticCompiler public

foldRelated :
  ∀ {ℓs ℓo ℓx ℓq ℓr}
    {SpecState : Set ℓs} {OptState : Set ℓo}
    {Input : Set ℓx} {Obs : Set ℓq}
    (C : LocalSemanticCompiler {ℓr = ℓr} SpecState OptState Input Obs)
    {s : SpecState} {o : OptState} →
    Related C s o →
    (xs : List Input) →
    Related C (fold (specStep C) s xs) (fold (optStep C) o xs)
foldRelated C rel []       = rel
foldRelated C rel (x ∷ xs) = foldRelated C (localLaw C x rel) xs

wholeFoldObservationPreserved :
  ∀ {ℓs ℓo ℓx ℓq ℓr}
    {SpecState : Set ℓs} {OptState : Set ℓo}
    {Input : Set ℓx} {Obs : Set ℓq}
    (C : LocalSemanticCompiler {ℓr = ℓr} SpecState OptState Input Obs)
    {s : SpecState} {o : OptState} →
    Related C s o →
    (xs : List Input) →
    observeSpec C (fold (specStep C) s xs)
      ≡ observeOpt C (fold (optStep C) o xs)
wholeFoldObservationPreserved C rel xs = consumerLaw C (foldRelated C rel xs)

------------------------------------------------------------------------
-- Separate resource compiler.
------------------------------------------------------------------------

record LocalResidencyBound : Set where
  constructor residency-bound
  field
    persistentState : Nat
    oneStreamItem   : Nat
    scratch         : Nat
    fixedRuntime    : Nat

open LocalResidencyBound public

peakResidencyBound : LocalResidencyBound → Nat
peakResidencyBound b =
  persistentState b + oneStreamItem b + scratch b + fixedRuntime b

peakBoundIsLocalSum :
  (b : LocalResidencyBound) →
  peakResidencyBound b
    ≡ persistentState b + oneStreamItem b + scratch b + fixedRuntime b
peakBoundIsLocalSum b = refl

record StreamingWorkShape : Set where
  constructor streaming-work
  field
    sourceItemCount : Nat
    liveItemCount   : Nat

open StreamingWorkShape public

-- This is the structural distinction needed by the Fly runs: source work may
-- grow with the number of domains/batches while the local residency theorem
-- mentions only one live stream item.  No asymptotic claim about total work is
-- manufactured from this record.
record StreamingResidencyCertificate : Set where
  constructor streaming-residency
  field
    workShape : StreamingWorkShape
    residency : LocalResidencyBound
    oneItemLive : liveItemCount workShape ≡ 1

------------------------------------------------------------------------
-- Error coordinates are intentionally non-collapsed.
------------------------------------------------------------------------

data OptimizationFailure : Set where
  semanticLawFailure
  foldCompositionFailure
  resourceBoundFailure
  resourceEnvelopeExhaustion
  performanceRegression : OptimizationFailure

record EmpiricalResourceWitness : Set where
  constructor empirical-resource
  field
    completed : Set
    -- Numeric RSS/time belong to execution receipts; this generic theorem does
    -- not import them into semantic correctness.

-- Principle carried from the RH/YM/Gödel proof-search corrections:
-- make the smallest local source/machine fact primitive and compile the large
-- consumer theorem from it.
