module DASHI.Physics.Benchmark where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.SymmetryQuotient as SQ

record BenchmarkTheory′ {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ) : Set (lsuc ℓ) where
  field
    Parameter  : Set ℓ
    Observable : Set ℓ
    Datum      : Observable → Set ℓ

    predictB :
      (p : Parameter) →
      (O : Observable) →
      SQ.PhysState Q →
      Datum O

record Dataset {ℓ : Level}
  (Obs : Set ℓ)
  (Datum : Obs → Set ℓ) : Set (lsuc ℓ) where
  field
    observed : (O : Obs) → Datum O

record BenchmarkMatch {ℓ : Level}
  {Q : SQ.QuotientedTheory ℓ}
  (B : BenchmarkTheory′ Q) : Set (lsuc ℓ) where
  open BenchmarkTheory′ B
  field
    Score : Set ℓ
    mismatch :
      (p : Parameter) →
      (x : SQ.PhysState Q) →
      Dataset Observable Datum →
      Score
