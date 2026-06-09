module DASHI.Physics.Closure.Gate2SpectralGapMath where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (*-identityˡ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Geometry.LCP.InductiveLimit using (NatColimitWitness)
import DASHI.Geometry.LCP.FiniteSpectralGap as FSG
import DASHI.Physics.Closure.SpectralGapRefinementStability as Spectral

------------------------------------------------------------------------
-- Gate 2 spectral-gap theorem package.
--
-- The existing finite spectral-gap toolkit already provides a concrete Bool
-- carrier with gap value 1, refinement monotonicity, and a Nat colimit
-- witness.  This module turns that into the lemma-shaped interface requested
-- for Gate 2: finite coercivity, refinement stability, and a colimit gap lift.
--
-- The construction is deliberately concrete and fail-closed.  It records the
-- finite theorem shape on the canonical Bool model and keeps the continuum
-- Yang-Mills theorem boundary outside the promoted surface.

gate2CanonicalGap : Nat
gate2CanonicalGap = suc zero

c : Nat → Nat
c _ = suc zero

gate2CanonicalToolkit :
  FSG.FiniteSpectralGapToolkit
gate2CanonicalToolkit =
  FSG.constantBoolFiniteSpectralGapToolkit

substω :
  {A : Set} →
  (P : A → Setω) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
substω P refl px = px

record GapProof (n Δn : Nat) : Setω where
  field
    canonicalToolkitRecorded :
      Bool

    canonicalToolkitRecordedIsTrue :
      canonicalToolkitRecorded ≡ true

    gapLowerBoundPositive :
      Δn ≡ suc zero

    coerciveLowerBound :
      Δn ≤ FSG.finiteHamiltonian
        gate2CanonicalToolkit
        n
        (FSG.excitedState gate2CanonicalToolkit n)

    vacuumEnergyZero :
      FSG.finiteHamiltonian
        gate2CanonicalToolkit
        n
        (FSG.groundState gate2CanonicalToolkit n)
      ≡
      zero

    projectionIncludesGroundState :
      FSG.groundStateInProjection gate2CanonicalToolkit n ≡ refl

    gapBoundary :
      List String

open GapProof public

record FiniteCoercivityWitness (n : Nat) : Setω where
  field
    gapValue :
      Nat

    gapProof :
      GapProof n gapValue

open FiniteCoercivityWitness public

canonicalGapProof :
  ∀ (n : Nat) →
  GapProof n gate2CanonicalGap
canonicalGapProof n =
  record
    { canonicalToolkitRecorded =
        true
    ; canonicalToolkitRecordedIsTrue =
        refl
    ; gapLowerBoundPositive =
        refl
    ; coerciveLowerBound =
        s≤s z≤n
    ; vacuumEnergyZero =
        refl
    ; projectionIncludesGroundState =
        refl
    ; gapBoundary =
        "Finite coercivity is witnessed on the canonical Bool carrier"
        ∷ "The ground state has zero energy and the excited state has gap 1"
        ∷ "Projection monotonicity is inherited from the finite toolkit"
        ∷ []
    }

FiniteCoercivity :
  ∀ (n : Nat) →
  FiniteCoercivityWitness n
FiniteCoercivity n =
  record
    { gapValue =
        gate2CanonicalGap
    ; gapProof =
        canonicalGapProof n
    }

GapRefinementInequality :
  ∀ {n Δn : Nat} →
  GapProof n Δn →
  GapProof (suc n) (c n * Δn)
GapRefinementInequality {n} {Δn} proof =
  substω
    (GapProof (suc n))
    (trans
      (sym (gapLowerBoundPositive proof))
      (sym (NatP.*-identityˡ Δn)))
    (canonicalGapProof (suc n))

record UniformLowerBound (Δ : Nat) : Setω where
  field
    canonicalToolkitRecorded :
      Bool

    canonicalToolkitRecordedIsTrue :
      canonicalToolkitRecorded ≡ true

    lowerBoundAtEveryDepth :
      ∀ (n : Nat) →
      Δ ≤ FSG.finiteHamiltonian
        gate2CanonicalToolkit
        n
        (FSG.excitedState gate2CanonicalToolkit n)

    natColimitWitness :
      NatColimitWitness (FSG.diagram gate2CanonicalToolkit)

    uniformBoundary :
      List String

open UniformLowerBound public

canonicalUniformLowerBound :
  UniformLowerBound gate2CanonicalGap
canonicalUniformLowerBound =
  record
    { canonicalToolkitRecorded =
        true
    ; canonicalToolkitRecordedIsTrue =
        refl
    ; lowerBoundAtEveryDepth =
        λ _ → s≤s z≤n
    ; natColimitWitness =
        FSG.limitWitness gate2CanonicalToolkit
    ; uniformBoundary =
        "The lower bound is uniform across the Nat tower"
        ∷ "The colimit witness is supplied by the constant Nat diagram"
        ∷ "The theorem is finite-to-limit shaped, not a continuum promotion"
        ∷ []
    }

record GapProof∞ (Δ : Nat) : Setω where
  field
    uniformLowerBound :
      UniformLowerBound Δ

    limitSpectrumShape :
      List String

    limitSpectrumShapeIsCanonical :
      limitSpectrumShape
      ≡
      "Spec(H∞) = {0} cup [Δ, infinity)"
      ∷ []

    gapLiftPromoted :
      Bool

    gapLiftPromotedIsFalse :
      gapLiftPromoted ≡ false

open GapProof∞ public

ColimitGapLift :
  ∀ {Δ : Nat} →
  UniformLowerBound Δ →
  GapProof∞ Δ
ColimitGapLift uniform =
  record
    { uniformLowerBound =
        uniform
    ; limitSpectrumShape =
        "Spec(H∞) = {0} cup [Δ, infinity)"
        ∷ []
    ; limitSpectrumShapeIsCanonical =
        refl
    ; gapLiftPromoted =
        false
    ; gapLiftPromotedIsFalse =
        refl
    }

record Gate2SpectralGapMathReceipt : Setω where
  field
    finiteCoercivityWitness :
      ∀ (n : Nat) →
      FiniteCoercivityWitness n

    gapRefinementInequalityWitness :
      ∀ {n Δn : Nat} →
      GapProof n Δn →
      GapProof (suc n) (c n * Δn)

    uniformLowerBoundWitness :
      UniformLowerBound gate2CanonicalGap

    colimitGapLiftWitness :
      GapProof∞ gate2CanonicalGap

    openObligations :
      List String

    proofBoundary :
      List String

open Gate2SpectralGapMathReceipt public

canonicalGate2SpectralGapMathReceipt :
  Gate2SpectralGapMathReceipt
canonicalGate2SpectralGapMathReceipt =
  record
    { finiteCoercivityWitness =
        FiniteCoercivity
    ; gapRefinementInequalityWitness =
        GapRefinementInequality
    ; uniformLowerBoundWitness =
        canonicalUniformLowerBound
    ; colimitGapLiftWitness =
        ColimitGapLift canonicalUniformLowerBound
    ; openObligations =
        "No continuum Yang-Mills promotion is claimed"
        ∷ "No positive-clay theorem is constructed here"
        ∷ []
    ; proofBoundary =
        "Gate 2 is implemented as finite coercivity, refinement stability, and colimit lift"
        ∷ "The module is concrete on the Bool model and fail-closed on the continuum claim"
        ∷ []
    }

gate2FirstFiniteCoercivity :
  FiniteCoercivityWitness zero
gate2FirstFiniteCoercivity =
  FiniteCoercivity zero
