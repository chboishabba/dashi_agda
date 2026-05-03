module DASHI.Physics.Closure.P0BlockadeProofObligations where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_)
open import Data.Product using (_×_; Σ)
open import Data.Sum using (_⊎_)

------------------------------------------------------------------------
-- Minimal P0 proof-obligation interfaces.
--
-- This module is deliberately generic.  It does not claim that any current
-- physics lane has discharged these obligations; it gives the small record
-- shapes that future blocker-specific modules can instantiate.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

iterate : {S : Set} → Nat → (S → S) → S → S
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

------------------------------------------------------------------------
-- P0.1: MDL seam / continuum aligned-carrier obligation.

record MDLSeam
  {Ccanon Cstar Cnoncanon : Set}
  : Set₁ where
  field
    φs : Ccanon → Cstar
    φn : Cstar → Cnoncanon
    ψ  : Ccanon → Cnoncanon

    mdlCanon : Ccanon → Nat
    mdlNoncanon : Cnoncanon → Nat

    commute :
      ∀ x → φn (φs x) ≡ ψ x

    mdlPreserved :
      ∀ x → mdlCanon x ≡ mdlNoncanon (ψ x)

------------------------------------------------------------------------
-- P0.2 / P0.3: finite convergence rate via an explicit natural-number bound.
--
-- `descent` alone does not construct `converges` for an arbitrary carrier;
-- the bounded convergence witness is the actual proof obligation.

record ConvergenceBound
  {S : Set}
  : Set₁ where
  field
    K : S → S
    mdl : S → Nat

    descent :
      ∀ x → mdl (K x) < mdl x ⊎ K x ≡ x

    fixedPoint : S

    converges :
      ∀ x →
      Σ Nat
        (λ n →
          iterate n K x ≡ fixedPoint
          ×
          n ≤ mdl x)

------------------------------------------------------------------------
-- P0.4: empirical adequacy bridge.

record EmpiricalAdequacy
  {S Obs : Set}
  : Set₁ where
  field
    fixedPoint : S
    obs : S → Obs
    empirical : Obs

    matches :
      obs fixedPoint ≡ empirical

------------------------------------------------------------------------
-- P0.5: p2 bridge or restricted obstruction.
--
-- An unrestricted obstruction over all functions A -> B is too strong:
-- `λ _ -> targetVal` is always a function when `targetVal` is available.
-- Real obstruction certificates therefore quantify over an admissible
-- candidate family.

record P2Bridge
  {A B : Set}
  : Set₁ where
  field
    β : A → B
    canonVal : A
    targetVal : B

    preserves :
      β canonVal ≡ targetVal

record P2Obstruction
  {A B : Set}
  (Candidate : (A → B) → Set)
  : Set₁ where
  field
    canonVal : A
    targetVal : B

    noBridge :
      ∀ β → Candidate β → β canonVal ≢ targetVal

data P2BridgeOrObstruction
  {A B : Set}
  (Candidate : (A → B) → Set)
  : Set₁ where
  positive :
    P2Bridge {A} {B} →
    P2BridgeOrObstruction Candidate
  obstructed :
    P2Obstruction {A} {B} Candidate →
    P2BridgeOrObstruction Candidate

------------------------------------------------------------------------
-- P0.6: atomic / chemistry witness promoted to a law.

record ChemistryLaw
  {Q C : Set}
  : Set₁ where
  field
    law : Q → Q → C
    trivialPair : Q → Q → C

    symmetric :
      ∀ x y → law x y ≡ law y x

    nontrivial :
      ∀ x y → law x y ≢ trivialPair x y

------------------------------------------------------------------------
-- P0.7: abstract / canonical field seam.

record FieldSeam
  {F : Set}
  : Setω where
  field
    gauge canonicalGauge : F → Set
    basin canonicalBasin : F → Set
    motif canonicalMotif : F → Set

    gaugeLaw :
      ∀ x → gauge x ≡ canonicalGauge x

    basinLaw :
      ∀ x → basin x ≡ canonicalBasin x

    motifLaw :
      ∀ x → motif x ≡ canonicalMotif x

------------------------------------------------------------------------
-- P0.8: realization independence as a parameterized noncanonical family.

record RealizationIndependence
  {S : Set}
  : Set₁ where
  field
    Kcanon : S → S
    Knoncanon : Nat → S → S

    mdl : S → Nat

    agrees :
      ∀ p x → mdl (Knoncanon p x) ≡ mdl (Kcanon x)

------------------------------------------------------------------------
-- P0.9: origin receipt as co-location, not new mathematics.

record OriginReceipt : Setω where
  field
    Source Carrier Obs Cstar Cnoncanon : Set

    mapToCarrier : Source → Carrier

    convergence :
      ConvergenceBound {Carrier}

    empirical :
      EmpiricalAdequacy {Carrier} {Obs}

    seam :
      MDLSeam {Carrier} {Cstar} {Cnoncanon}
