module DASHI.Geometry.Signature.ConeArrowInstances where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _<_)
open import Data.Vec using (Vec)

open import DASHI.Geometry.ConeTimeIsotropy
open import DASHI.Geometry.Signature.HyperbolicForm as HF

-- Concrete carrier: causal counts with 3 spatial components.
V : Set
V = HF.CausalCounts 3

-- Cone: hyperbolic bound at fixed speed c (parametric).
coneStructure : ℕ → ConeStructure V
coneStructure c =
  record
    { Cone = HF.ConeBound c
    ; ConeNontrivial = tt
    }

-- Arrow: time increases (tau strictly increases).
timeArrow : TimeArrow V
timeArrow =
  record
    { _≺_ = λ x y → HF.tau x < HF.tau y
    ; Irreflexive = λ _ → tt
    ; Transitive = λ _ _ _ → tt
    }

-- Isotropy: trivial action (placeholder concrete instance).
isotropyTrivial : IsotropyAction V
isotropyTrivial =
  record
    { G = ⊤
    ; _•_ = λ _ x → x
    ; PresCone = λ _ _ → tt
    ; PresQ = λ _ _ → tt
    }
