module DASHI.Physics.FiniteAlgebraCandidates where

open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Minimal finite-algebra candidate list scaffold (R, C, H).
data BaseField : Set where
  R : BaseField
  C : BaseField
  H : BaseField

record MatrixAlg : Set where
  field
    base : BaseField
    n    : Nat
open MatrixAlg public

record DirectSum : Set where
  field
    A B : MatrixAlg
open DirectSum public

-- A small, explicit candidate list (extend as needed).
candidateAlgebras : Set
candidateAlgebras = MatrixAlg

-- Example candidates: M₁(R), M₂(C), M₁(H), etc.
M1R : MatrixAlg
M1R = record { base = R ; n = suc zero }

M2C : MatrixAlg
M2C = record { base = C ; n = suc (suc zero) }

M1H : MatrixAlg
M1H = record { base = H ; n = suc zero }

-- A few direct sums as placeholders for finite algebra classification.
M1R⊕M2C : DirectSum
M1R⊕M2C = record { A = M1R ; B = M2C }

M2C⊕M1H : DirectSum
M2C⊕M1H = record { A = M2C ; B = M1H }
