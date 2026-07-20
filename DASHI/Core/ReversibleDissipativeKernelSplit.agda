{-# OPTIONS --safe #-}
module DASHI.Core.ReversibleDissipativeKernelSplit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)

------------------------------------------------------------------------
-- Reversible evolution and observation/selection are separate operators.
-- This prevents contraction, pruning, or measurement from being silently
-- identified with unitary/Hamiltonian evolution.

record ReversibleKernel (S : Set) : Set₁ where
  field
    evolve : S → S
    reverse : S → S
    reverse-evolve : ∀ x → reverse (evolve x) ≡ x
    evolve-reverse : ∀ x → evolve (reverse x) ≡ x
open ReversibleKernel public

record ObservationKernel (S : Set) : Set₁ where
  field
    observe : S → S
    idempotent : ∀ x → observe (observe x) ≡ observe x
open ObservationKernel public

selectedEvolution :
  ∀ {S} → ReversibleKernel S → ObservationKernel S → S → S
selectedEvolution U M x = observe M (evolve U x)

reversible-injective :
  ∀ {S} (U : ReversibleKernel S) {x y : S} →
  evolve U x ≡ evolve U y → x ≡ y
reversible-injective U {x} {y} exy =
  trans
    (symmetry (reverse-evolve U x))
    (trans (cong (reverse U) exy) (reverse-evolve U y))
  where
    symmetry : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
    symmetry refl = refl

record ReversibleDissipativeSplit (S : Set) : Set₁ where
  constructor reversible-dissipative-split
  field
    reversiblePart : ReversibleKernel S
    observationPart : ObservationKernel S
    fullStep : S → S
    fullStep-factorises :
      ∀ x → fullStep x ≡ selectedEvolution reversiblePart observationPart x
open ReversibleDissipativeSplit public

identityReversible : ∀ {S} → ReversibleKernel S
identityReversible =
  record
    { evolve = λ x → x
    ; reverse = λ x → x
    ; reverse-evolve = λ _ → refl
    ; evolve-reverse = λ _ → refl
    }

identityObservation : ∀ {S} → ObservationKernel S
identityObservation =
  record
    { observe = λ x → x
    ; idempotent = λ _ → refl
    }

identitySplit : ∀ {S} → ReversibleDissipativeSplit S
identitySplit =
  reversible-dissipative-split
    identityReversible
    identityObservation
    (λ x → x)
    (λ _ → refl)

record KernelSplitClaimBoundary : Set where
  constructor kernel-split-claim-boundary
  field
    reversibleEvolutionSeparated : Bool
    reversibleEvolutionSeparatedIsTrue : reversibleEvolutionSeparated ≡ true
    everyContractiveKernelIsUnitary : Bool
    everyContractiveKernelIsUnitaryIsFalse : everyContractiveKernelIsUnitary ≡ false
    observationIsGloballyInformationPreserving : Bool
    observationIsGloballyInformationPreservingIsFalse :
      observationIsGloballyInformationPreserving ≡ false
    mdlDescentIsHamiltonianEvolution : Bool
    mdlDescentIsHamiltonianEvolutionIsFalse : mdlDescentIsHamiltonianEvolution ≡ false
open KernelSplitClaimBoundary public

canonicalKernelSplitBoundary : KernelSplitClaimBoundary
canonicalKernelSplitBoundary =
  kernel-split-claim-boundary
    true refl
    false refl
    false refl
    false refl
