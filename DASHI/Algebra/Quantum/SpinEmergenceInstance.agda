module DASHI.Algebra.Quantum.SpinEmergenceInstance where

open import Data.Unit.Polymorphic using (⊤; tt)
open import Agda.Builtin.Equality using (refl)
open import Data.Integer using (ℤ; _+_; _*_; +_)

open import DASHI.Algebra.Quantum.SpinEmergence
open import DASHI.Geometry.Clifford.SpinFromSignature as SFS

-- Minimal concrete SpinFromSignature instance.
spinFromSignature : SFS.SpinFromSignature
spinFromSignature =
  record
    { B = record { V = ⊤ ; g = λ _ _ → (+ 0) }
    ; Clif =
        record
          { Cl = ⊤
          ; one = tt
          ; mul = λ _ _ → tt
          ; add = λ _ _ → tt
          ; embed = λ _ → tt
          ; scalar = λ _ → tt
          ; rel = λ _ _ → refl
          }
    ; Spin = ⊤
    ; SO31 = ⊤
    ; cover = λ _ → tt
    ; doubleCover = ⊤
    }

spinEmergenceAxioms : SpinEmergenceAxioms
spinEmergenceAxioms =
  record
    { QuadraticForm = ⊤
    ; Signature31 = tt
    ; CliffordAlgebra = λ _ → SFS.Clifford (SFS.SpinFromSignature.B spinFromSignature)
    ; SpinGroup = SFS.SpinFromSignature.Spin spinFromSignature
    ; SO = λ _ _ → ⊤
    ; SpinIsDoubleCover = λ _ → tt
    }
