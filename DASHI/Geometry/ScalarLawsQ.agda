module DASHI.Geometry.ScalarLawsQ where

open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_; 0ℚ; 1ℚ; _-ℚ_)
import Data.Rational.Properties as Rₚ

open import DASHI.Geometry.EnergyAdditivityProof

-- ScalarField instance for ℚ.
scalarFieldℚ : ScalarField
scalarFieldℚ =
  record
    { Scalar = ℚ
    ; _+s_ = _+ℚ_
    ; _*s_ = _*ℚ_
    ; 0s = 0ℚ
    ; 1s = 1ℚ
    ; -s_ = λ x → _-ℚ_ 0ℚ x
    }

-- Scalar laws for ℚ (associativity, commutativity, identity).
scalarLawsℚ : ScalarLaws scalarFieldℚ
scalarLawsℚ =
  record
    { +s-assoc = Rₚ.+-assoc
    ; +s-comm = Rₚ.+-comm
    ; +s-idL = Rₚ.+-identityˡ
    }
