module DASHI.Algebra.SMConformanceVectorsInstance where

open import DASHI.Algebra.SMConformanceVectors
open import DASHI.Algebra.PhysicsTable
open import DASHI.Algebra.PhysicsSignature using (Sig15)

smConformanceAxioms : SMConformanceAxioms
smConformanceAxioms =
  record
    { State = State
    ; Sig = Sig15
    ; specSig = specSig
    ; implSig = implSig
    ; vectors = vectors
    ; physics-conformance = physics-conformance
    }
