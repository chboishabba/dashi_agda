module DASHI.Physics.BianchiEinsteinAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤)

------------------------------------------------------------------------
-- Abstract “discrete geometry” interface for the Einstein gate
------------------------------------------------------------------------

record DiscreteManifoldLike (V : Set) : Set₁ where
  field
    Metric    : Set
    Tensor2   : Set
    Scalar    : Set
    Laplacian : Scalar → Scalar
    Div       : Tensor2 → Scalar
    Sym       : Tensor2 → Set
    zeroS     : Scalar

------------------------------------------------------------------------
-- Gate seams
------------------------------------------------------------------------

record EinsteinGate {V : Set} (M : DiscreteManifoldLike V) : Set₁ where
  open DiscreteManifoldLike M
  field
    R      : Scalar → Scalar
    G      : Tensor2
    T      : Tensor2
    bianchi : Div G ≡ zeroS
    symG    : Sym G
    lovelock-unique : ⊤

record EinsteinAxioms : Set₁ where
  field
    EinsteinEquation :
      ∀ {Dim : Nat} {V : Set} →
      DiscreteManifoldLike V → Set

EinsteinEquation :
  (A : EinsteinAxioms) →
  ∀ {Dim : Nat} {V : Set} →
  DiscreteManifoldLike V → Set
EinsteinEquation A {Dim} {V} = EinsteinAxioms.EinsteinEquation A {Dim} {V}

einsteinAxiomsDefault : EinsteinAxioms
einsteinAxiomsDefault =
  record
    { EinsteinEquation = λ {Dim} {V} _ → ⊤ }
