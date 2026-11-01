module DASHI.Foundations.InvolutiveTernaryRenormalisation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- A generic scale-indexed involutive carrier tower.
--
-- The maps are intentionally called coarse rather than quotient: an
-- application may instantiate them as blocking, substitution, projection,
-- p-adic prefix truncation, or another recognisable macro construction.

record InvolutiveScaleTower : Set₁ where
  field
    Carrier : Nat → Set

    ι : ∀ j → Carrier j → Carrier j
    ι-involutive : ∀ j x → ι j (ι j x) ≡ x

    coarse : ∀ j → Carrier j → Carrier (suc j)
    coarse-equivariant :
      ∀ j x →
      coarse j (ι j x) ≡ ι (suc j) (coarse j x)

open InvolutiveScaleTower public

------------------------------------------------------------------------
-- Lifted dynamics commuting with coarse graining.

record LiftedInvolutiveDynamics (T : InvolutiveScaleTower) : Set₁ where
  field
    Control : Nat → Set

    controlι : ∀ j → Control j → Control j
    controlι-involutive : ∀ j u → controlι j (controlι j u) ≡ u

    liftControl : ∀ j → Control j → Control (suc j)
    liftControl-equivariant :
      ∀ j u →
      liftControl j (controlι j u) ≡
      controlι (suc j) (liftControl j u)

    step : ∀ j → Carrier T j → Control j → Carrier T j

    step-equivariant :
      ∀ j s u →
      step j (ι T j s) (controlι j u) ≡
      ι T j (step j s u)

    coarse-step-commutes :
      ∀ j s u →
      coarse T j (step j s u) ≡
      step (suc j) (coarse T j s) (liftControl j u)

open LiftedInvolutiveDynamics public

------------------------------------------------------------------------
-- Scale-indexed invariants and admissibility.

record InvariantTower
  (T : InvolutiveScaleTower)
  (D : LiftedInvolutiveDynamics T) : Set₁ where
  field
    Value : Nat → Set
    read : ∀ j → Carrier T j → Value j

    transition-invariant :
      ∀ j s u →
      read j (step D j s u) ≡ read j s

open InvariantTower public

record AdmissibilityTower (T : InvolutiveScaleTower) : Set₁ where
  field
    Admissible : ∀ j → Carrier T j → Set

    coarse-preserves-admissible :
      ∀ j s →
      Admissible j s →
      Admissible (suc j) (coarse T j s)

    mirror-preserves-admissible :
      ∀ j s →
      Admissible j s →
      Admissible j (ι T j s)

open AdmissibilityTower public

------------------------------------------------------------------------
-- Finite recognisability contract.
--
-- Rather than asserting unique decomposition globally, this record asks an
-- instantiation to provide a decoder and exact section law.  Local-radius
-- recognisability can be layered on top once a concrete neighbourhood carrier
-- is chosen.

record RecognisableScaleStep
  (T : InvolutiveScaleTower)
  (j : Nat) : Set₁ where
  field
    refine : Carrier T (suc j) → Carrier T j
    coarse-refine : ∀ macro → coarse T j (refine macro) ≡ macro

open RecognisableScaleStep public

------------------------------------------------------------------------
-- A compact receipt surface preserving claim boundaries.

record RenormalisationTowerBoundary : Set where
  constructor boundary
  field
    involutionCommutesWithCoarseMap : Bool
    dynamicsCommutesWithCoarseMap : Bool
    recognisabilityMustBeInstantiated : Bool
    logarithmicPruningClaimPromoted : Bool
    renormalisationPhysicsPromoted : Bool

canonicalBoundary : RenormalisationTowerBoundary
canonicalBoundary = boundary true true true false false
