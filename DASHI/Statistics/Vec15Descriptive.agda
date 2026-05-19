module DASHI.Statistics.Vec15Descriptive where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_∸_)

open import DASHI.Statistics.Vec15Order public using
  ( PrimeCarrier15
  ; median15
  ; lowerQuartile15
  ; upperQuartile15
  ; rank15
  )

open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- Core descriptive surface for the 15-prime carrier.
--
-- The constructive part covers:
--   - total mass
--   - pointwise extrema
--   - spread/range
--   - non-zero count
--   - order selection and rank

sum15 : PrimeCarrier15 → Nat
sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 + a3 + a5 + a7 + a11 + a13 + a17 + a19 + a23 + a29 + a31 + a41 + a47 + a59 + a71

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

minNat : Nat → Nat → Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

max15 : PrimeCarrier15 → Nat
max15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  maxNat a2
    (maxNat a3
      (maxNat a5
        (maxNat a7
          (maxNat a11
            (maxNat a13
              (maxNat a17
                (maxNat a19
                  (maxNat a23
                    (maxNat a29
                      (maxNat a31
                        (maxNat a41
                          (maxNat a47
                            (maxNat a59 a71)))))))))))))

min15 : PrimeCarrier15 → Nat
min15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  minNat a2
    (minNat a3
      (minNat a5
        (minNat a7
          (minNat a11
            (minNat a13
              (minNat a17
                (minNat a19
                  (minNat a23
                    (minNat a29
                      (minNat a31
                        (minNat a41
                          (minNat a47
                            (minNat a59 a71)))))))))))))

range15 : PrimeCarrier15 → Nat
range15 v = max15 v ∸ min15 v

countNonZeroNat : Nat → Nat
countNonZeroNat zero = zero
countNonZeroNat (suc _) = suc zero

countNonZero15 : PrimeCarrier15 → Nat
countNonZero15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  countNonZeroNat a2 + countNonZeroNat a3 + countNonZeroNat a5 + countNonZeroNat a7 +
  countNonZeroNat a11 + countNonZeroNat a13 + countNonZeroNat a17 + countNonZeroNat a19 +
  countNonZeroNat a23 + countNonZeroNat a29 + countNonZeroNat a31 + countNonZeroNat a41 +
  countNonZeroNat a47 + countNonZeroNat a59 + countNonZeroNat a71
