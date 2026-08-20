module DASHI.Geometry.Gauge.M6BitensorRepresentation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_)

congEq : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
congEq f refl = refl

symEq : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

-- M3 is a single admissible carrier. Its mirror is supplied explicitly;
-- no identification of a carrier with its dual is assumed.
record M3Carrier {g ℓ : Level} (G : Set g) : Set (g ⊔ lsuc ℓ) where
  field
    Carrier : Set ℓ
    mirror  : Carrier → Carrier
    mirror-involutive : (x : Carrier) → mirror (mirror x) ≡ x
    act     : G → Carrier → Carrier

-- An M6 point is the oriented carrier/mirror pair. This is the finite,
-- proof-relevant carrier of V ⊗ V*; geometric implementations may index the
-- two factors by distinct base points.
M6Point : ∀ {g ℓ} {G : Set g} → M3Carrier {g} {ℓ} G → Set ℓ
M6Point C = M3Carrier.Carrier C × M3Carrier.Carrier C

record M6Bitensor {g ℓ s : Level} (G : Set g)
                    (C : M3Carrier {g} {ℓ} G) : Set (g ⊔ ℓ ⊔ lsuc s) where
  field
    Shell : Set s
    shellOf : M6Point C → Shell
    diagonalAct : G → M6Point C → M6Point C
    shellCovariant : (h : G) (p : M6Point C) →
      shellOf (diagonalAct h p) ≡ shellOf p

-- Highest-weight implementations instantiate Weight with their weight type.
-- The diagonal M6 weight is μ - ν; subtraction is abstract because a weight
-- lattice need not be Nat-valued.
record WeightDifference {w : Level} (Weight : Set w) : Set (lsuc w) where
  field
    _−w_ : Weight → Weight → Weight

record M6WeightPair {w : Level} (Weight : Set w) : Set w where
  constructor weight-pair
  field
    leftWeight  : Weight
    rightWeight : Weight

open M6WeightPair public

DiagonalWeight : ∀ {w} {Weight : Set w} →
  WeightDifference Weight → M6WeightPair Weight → Weight
DiagonalWeight D p =
  WeightDifference._−w_ D (leftWeight p) (rightWeight p)

-- A shell is saturated when every internal state is sent to the same central
-- representative. This captures Haar/Schur collapse without postulating an
-- integral in the representation-independent core.
record ShellSaturation {s x : Level} (Shell : Set s) (X : Set x)
  : Set (s ⊔ lsuc x) where
  field
    centre     : Shell → X
    saturate   : Shell → X → X
    collapse   : (σ : Shell) (x : X) → saturate σ x ≡ centre σ

  idempotent : (σ : Shell) (x : X) →
    saturate σ (saturate σ x) ≡ saturate σ x
  idempotent σ x =
    transEq
      (congEq (saturate σ) (collapse σ x))
      (transEq (collapse σ (centre σ)) (symEq (collapse σ x)))

  centre-fixed : (σ : Shell) → saturate σ (centre σ) ≡ centre σ
  centre-fixed σ = collapse σ (centre σ)

-- The noncentral part is exactly the unsaturated residue.
record M6Residue {s x : Level} (Shell : Set s) (X : Set x)
                 (Sat : ShellSaturation Shell X) : Set (s ⊔ x) where
  field
    shell : Shell
    state : X
    isUnsaturated : Bool
    unsaturatedIsTrue : isUnsaturated ≡ true

-- Dimension bookkeeping for a finite representation decomposition.
record ShellDimension : Set where
  constructor shell-dimension
  field
    shellDimension : Nat
    multiplicity   : Nat
