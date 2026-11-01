module DASHI.Geometry.LCP.FiniteSpectralGap where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Geometry.LCP.InductiveLimit using
  (NatDiagram; NatColimitWitness; constantNatDiagram;
   constantNatColimitWitness; natDirectedness)

------------------------------------------------------------------------
-- Finite spectral-gap toolkit.
--
-- This is intentionally narrower than a full spectral theorem.  It packages
-- the finite-volume Hamiltonian data, a gap lower bound, refinement
-- monotonicity, and the transfer of the family to an inductive limit.
--
-- The concrete model is a constant Nat-indexed Bool carrier with a two-level
-- Hamiltonian.  The gap is genuinely finite and typed, but the continuum
-- Yang-Mills claim remains outside this module.

record FiniteSpectralGapToolkit : Setω where
  field
    diagram :
      NatDiagram

    jointRefinement :
      ∀ (m n : ℕ) →
      Σ ℕ (λ k → (m ≤ k) × (n ≤ k))

    refinement :
      ∀ {m n : ℕ} →
      m ≤ n →
      NatDiagram.Obj diagram m →
      NatDiagram.Obj diagram n

    refinementIsMap :
      ∀ {m n : ℕ} →
      (m≤n : m ≤ n) →
      (x : NatDiagram.Obj diagram m) →
      refinement m≤n x ≡ NatDiagram.map diagram m≤n x

    finiteHamiltonian :
      (n : ℕ) →
      NatDiagram.Obj diagram n →
      ℕ

    groundState :
      (n : ℕ) →
      NatDiagram.Obj diagram n

    excitedState :
      (n : ℕ) →
      NatDiagram.Obj diagram n

    groundEnergyZero :
      (n : ℕ) →
      finiteHamiltonian n (groundState n) ≡ zero

    excitedStateDistinct :
      (n : ℕ) →
      excitedState n ≡ groundState n →
      ⊥

    spectralGapLowerBound :
      ℕ

    spectralGapLowerBoundPositive :
      spectralGapLowerBound ≡ suc zero

    excitedStateLowerBound :
      (n : ℕ) →
      spectralGapLowerBound ≤ finiteHamiltonian n (excitedState n)

    spectralProjection :
      (n : ℕ) →
      ℕ →
      NatDiagram.Obj diagram n →
      Bool

    groundStateInProjection :
      (n : ℕ) →
      spectralProjection n spectralGapLowerBound (groundState n) ≡ true

    projectionMonotoneUnderRefinement :
      ∀ {m n : ℕ} →
      (m≤n : m ≤ n) →
      (k : ℕ) →
      (x : NatDiagram.Obj diagram m) →
      spectralProjection m k x ≡ true →
      spectralProjection n k (refinement m≤n x) ≡ true

    limitWitness :
      NatColimitWitness diagram

    toolkitBoundary :
      List String

open FiniteSpectralGapToolkit public

boolFiniteHamiltonian :
  ℕ →
  Bool →
  ℕ
boolFiniteHamiltonian _ false = zero
boolFiniteHamiltonian _ true = suc zero

boolSpectralProjection :
  ℕ →
  ℕ →
  Bool →
  Bool
boolSpectralProjection _ _ false = true
boolSpectralProjection _ zero true = false
boolSpectralProjection _ (suc _) true = true

boolProjectionMonotoneUnderRefinement :
  ∀ {m n : ℕ} →
  (m≤n : m ≤ n) →
  (k : ℕ) →
  (x : Bool) →
  boolSpectralProjection m k x ≡ true →
  boolSpectralProjection n k x ≡ true
boolProjectionMonotoneUnderRefinement _ k false hyp = refl
boolProjectionMonotoneUnderRefinement _ zero true hyp = hyp
boolProjectionMonotoneUnderRefinement _ (suc _) true hyp = refl

constantBoolFiniteSpectralGapToolkit :
  FiniteSpectralGapToolkit
constantBoolFiniteSpectralGapToolkit =
  record
    { diagram = constantNatDiagram Bool
    ; jointRefinement = natDirectedness
    ; refinement = λ _ x → x
    ; refinementIsMap = λ _ _ → refl
    ; finiteHamiltonian = boolFiniteHamiltonian
    ; groundState = λ _ → false
    ; excitedState = λ _ → true
    ; groundEnergyZero = λ _ → refl
    ; excitedStateDistinct = λ _ ()
    ; spectralGapLowerBound = suc zero
    ; spectralGapLowerBoundPositive = refl
    ; excitedStateLowerBound = λ _ → s≤s z≤n
    ; spectralProjection = boolSpectralProjection
    ; groundStateInProjection = λ _ → refl
    ; projectionMonotoneUnderRefinement =
        boolProjectionMonotoneUnderRefinement
    ; limitWitness = constantNatColimitWitness Bool
    ; toolkitBoundary =
        "FiniteSpectralGapToolkit packages finite-volume Hamiltonian data"
        ∷ "The concrete model is Bool-valued, two-level, and Nat-indexed"
        ∷ "The common-upper-bound structure is reused from the inductive-limit layer"
        ∷ "The colimit transfer is concretely witnessed by the constant Nat colimit"
        ∷ "This module does not claim the full Yang-Mills spectral theorem"
        ∷ []
    }

constantBoolFiniteSpectralGapBoundary :
  List String
constantBoolFiniteSpectralGapBoundary =
  "Finite spectral-gap toolkit is concrete and finite"
  ∷ "Gap lower bound is fixed at 1 on the Bool carrier"
  ∷ "Inductive-limit transfer is staged through the Nat colimit witness"
  ∷ []
