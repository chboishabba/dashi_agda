module DASHI.Geometry.Signature.Signature31Instance where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; replicate)
open import Relation.Binary.PropositionalEquality using (refl)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.Signature.HyperbolicForm as HF
open import DASHI.Geometry.Signature.ConeArrowInstances as CAI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31

-- Minimal additive + scalar structures for the carrier V.
AdditiveV : Additive _
AdditiveV =
  record
    { Carrier = CAI.V
    ; _+_ = λ x y →
        record
          { tau = HF.tau x + HF.tau y
          ; sigma = HF.sigma x
          }
    ; 0# = record { tau = 0 ; sigma = replicate 3 0 }
    ; -_ = λ x → x
    }

ScalarNat : ScalarField _
ScalarNat =
  record
    { S = ℕ
    ; _+s_ = _+_
    ; _*s_ = _*_
    ; 0s = 0
    ; 1s = 1
    ; -s_ = λ n → n
    }

-- A trivial quadratic form placeholder on the carrier.
QF : QuadraticForm AdditiveV ScalarNat
QF =
  record
    { Q = λ _ → 0
    ; Parallelogram = λ _ _ → refl
    ; Homog = λ _ _ → tt
    }

sigAxioms : S31.SignatureAxioms AdditiveV ScalarNat QF
sigAxioms =
  record
    { ConeS = CAI.coneStructure 1
    ; Arrow = CAI.timeArrow
    ; Iso = CAI.isotropyTrivial
    ; Timelike↔Cone = λ _ → tt
    }

sig31Axioms : S31.Signature31FromConeArrowIsotropyAxioms AdditiveV ScalarNat QF
sig31Axioms =
  record
    { Signature31Theorem = λ _ → CTI.sig31
    }

signature31 : CTI.Signature
signature31 = S31.Signature31Theorem AdditiveV ScalarNat QF sigAxioms sig31Axioms
