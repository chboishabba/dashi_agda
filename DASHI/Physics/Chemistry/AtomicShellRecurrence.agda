module DASHI.Physics.Chemistry.AtomicShellRecurrence where

-- Periodicity is represented as recurrence of valence classes across
-- shell-completion events.  It is not asserted to be one global fixed-period
-- translation symmetry.

record AtomicShellRecurrence : Set₁ where
  field
    AtomicState       : Set
    Shell             : Set
    ValenceClass      : Set
    CompletionStep    : AtomicState → AtomicState → Set

    shellOf           : AtomicState → Shell
    valenceOf         : AtomicState → ValenceClass

    fermionAdmissible : AtomicState → Set
    shellClosed       : AtomicState → Set
    openShell         : AtomicState → Set

    completionPreservesAdmissibility :
      ∀ {x y} → CompletionStep x y →
      fermionAdmissible x → fermionAdmissible y

    recurrentValence :
      ∀ {x y} → CompletionStep x y →
      shellClosed x → Set

-- Closed-shell locking is exposed through a projector-level interface rather
-- than through stability of an arbitrary hand-written orbital list.
record ClosedShellProjectionLock
  (S : AtomicShellRecurrence) : Set₁ where
  open AtomicShellRecurrence S
  field
    Perturbation      : Set
    OccupiedProjector : AtomicState → Set
    GapWitness        : AtomicState → Set
    SmallRelativeToGap : Perturbation → AtomicState → Set
    PerturbedState    : Perturbation → AtomicState → AtomicState

    rankStable :
      ∀ {δ x} → shellClosed x → GapWitness x →
      SmallRelativeToGap δ x → Set

    valenceClassStable :
      ∀ {δ x} → shellClosed x → GapWitness x →
      SmallRelativeToGap δ x →
      valenceOf (PerturbedState δ x) ≡ valenceOf x

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
