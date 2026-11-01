module DASHI.Foundations.TernaryGolay.NonaryTernaryReduction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high
  ; NonaryTruth ; non-0 ; non-1 ; non-2 ; non-3 ; non-4
  ; non-5 ; non-6 ; non-7 ; non-8
  )
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.Base369NonaryTruthRing as Z9

------------------------------------------------------------------------
-- The genuine arithmetic 9 -> 3 bridge.
--
-- This is a ring reduction, unlike the UBP nine-channel codec. Each ternary
-- value has a three-element fibre in Z/9Z.
------------------------------------------------------------------------

reduce9to3 : NonaryTruth → TriTruth
reduce9to3 non-0 = tri-low
reduce9to3 non-1 = tri-mid
reduce9to3 non-2 = tri-high
reduce9to3 non-3 = tri-low
reduce9to3 non-4 = tri-mid
reduce9to3 non-5 = tri-high
reduce9to3 non-6 = tri-low
reduce9to3 non-7 = tri-mid
reduce9to3 non-8 = tri-high

section3to9 : TriTruth → NonaryTruth
section3to9 tri-low = non-0
section3to9 tri-mid = non-1
section3to9 tri-high = non-2

reduceSection : (x : TriTruth) → reduce9to3 (section3to9 x) ≡ x
reduceSection tri-low = refl
reduceSection tri-mid = refl
reduceSection tri-high = refl

reductionFibreLow : List NonaryTruth
reductionFibreLow = non-0 ∷ non-3 ∷ non-6 ∷ []

reductionFibreMid : List NonaryTruth
reductionFibreMid = non-1 ∷ non-4 ∷ non-7 ∷ []

reductionFibreHigh : List NonaryTruth
reductionFibreHigh = non-2 ∷ non-5 ∷ non-8 ∷ []

reducePreservesZero : reduce9to3 Z9.nonaryZero ≡ F3.triZero
reducePreservesZero = refl

reducePreservesOne : reduce9to3 Z9.nonaryOne ≡ F3.triOne
reducePreservesOne = refl

reducePreservesAdd :
  (a b : NonaryTruth) →
  reduce9to3 (Z9.nonaryAdd a b)
  ≡ F3.triAdd (reduce9to3 a) (reduce9to3 b)
reducePreservesAdd non-0 non-0 = refl
reducePreservesAdd non-0 non-1 = refl
reducePreservesAdd non-0 non-2 = refl
reducePreservesAdd non-0 non-3 = refl
reducePreservesAdd non-0 non-4 = refl
reducePreservesAdd non-0 non-5 = refl
reducePreservesAdd non-0 non-6 = refl
reducePreservesAdd non-0 non-7 = refl
reducePreservesAdd non-0 non-8 = refl
reducePreservesAdd non-1 non-0 = refl
reducePreservesAdd non-1 non-1 = refl
reducePreservesAdd non-1 non-2 = refl
reducePreservesAdd non-1 non-3 = refl
reducePreservesAdd non-1 non-4 = refl
reducePreservesAdd non-1 non-5 = refl
reducePreservesAdd non-1 non-6 = refl
reducePreservesAdd non-1 non-7 = refl
reducePreservesAdd non-1 non-8 = refl
reducePreservesAdd non-2 non-0 = refl
reducePreservesAdd non-2 non-1 = refl
reducePreservesAdd non-2 non-2 = refl
reducePreservesAdd non-2 non-3 = refl
reducePreservesAdd non-2 non-4 = refl
reducePreservesAdd non-2 non-5 = refl
reducePreservesAdd non-2 non-6 = refl
reducePreservesAdd non-2 non-7 = refl
reducePreservesAdd non-2 non-8 = refl
reducePreservesAdd non-3 non-0 = refl
reducePreservesAdd non-3 non-1 = refl
reducePreservesAdd non-3 non-2 = refl
reducePreservesAdd non-3 non-3 = refl
reducePreservesAdd non-3 non-4 = refl
reducePreservesAdd non-3 non-5 = refl
reducePreservesAdd non-3 non-6 = refl
reducePreservesAdd non-3 non-7 = refl
reducePreservesAdd non-3 non-8 = refl
reducePreservesAdd non-4 non-0 = refl
reducePreservesAdd non-4 non-1 = refl
reducePreservesAdd non-4 non-2 = refl
reducePreservesAdd non-4 non-3 = refl
reducePreservesAdd non-4 non-4 = refl
reducePreservesAdd non-4 non-5 = refl
reducePreservesAdd non-4 non-6 = refl
reducePreservesAdd non-4 non-7 = refl
reducePreservesAdd non-4 non-8 = refl
reducePreservesAdd non-5 non-0 = refl
reducePreservesAdd non-5 non-1 = refl
reducePreservesAdd non-5 non-2 = refl
reducePreservesAdd non-5 non-3 = refl
reducePreservesAdd non-5 non-4 = refl
reducePreservesAdd non-5 non-5 = refl
reducePreservesAdd non-5 non-6 = refl
reducePreservesAdd non-5 non-7 = refl
reducePreservesAdd non-5 non-8 = refl
reducePreservesAdd non-6 non-0 = refl
reducePreservesAdd non-6 non-1 = refl
reducePreservesAdd non-6 non-2 = refl
reducePreservesAdd non-6 non-3 = refl
reducePreservesAdd non-6 non-4 = refl
reducePreservesAdd non-6 non-5 = refl
reducePreservesAdd non-6 non-6 = refl
reducePreservesAdd non-6 non-7 = refl
reducePreservesAdd non-6 non-8 = refl
reducePreservesAdd non-7 non-0 = refl
reducePreservesAdd non-7 non-1 = refl
reducePreservesAdd non-7 non-2 = refl
reducePreservesAdd non-7 non-3 = refl
reducePreservesAdd non-7 non-4 = refl
reducePreservesAdd non-7 non-5 = refl
reducePreservesAdd non-7 non-6 = refl
reducePreservesAdd non-7 non-7 = refl
reducePreservesAdd non-7 non-8 = refl
reducePreservesAdd non-8 non-0 = refl
reducePreservesAdd non-8 non-1 = refl
reducePreservesAdd non-8 non-2 = refl
reducePreservesAdd non-8 non-3 = refl
reducePreservesAdd non-8 non-4 = refl
reducePreservesAdd non-8 non-5 = refl
reducePreservesAdd non-8 non-6 = refl
reducePreservesAdd non-8 non-7 = refl
reducePreservesAdd non-8 non-8 = refl

reducePreservesMul :
  (a b : NonaryTruth) →
  reduce9to3 (Z9.nonaryMul a b)
  ≡ F3.triMul (reduce9to3 a) (reduce9to3 b)
reducePreservesMul non-0 non-0 = refl
reducePreservesMul non-0 non-1 = refl
reducePreservesMul non-0 non-2 = refl
reducePreservesMul non-0 non-3 = refl
reducePreservesMul non-0 non-4 = refl
reducePreservesMul non-0 non-5 = refl
reducePreservesMul non-0 non-6 = refl
reducePreservesMul non-0 non-7 = refl
reducePreservesMul non-0 non-8 = refl
reducePreservesMul non-1 non-0 = refl
reducePreservesMul non-1 non-1 = refl
reducePreservesMul non-1 non-2 = refl
reducePreservesMul non-1 non-3 = refl
reducePreservesMul non-1 non-4 = refl
reducePreservesMul non-1 non-5 = refl
reducePreservesMul non-1 non-6 = refl
reducePreservesMul non-1 non-7 = refl
reducePreservesMul non-1 non-8 = refl
reducePreservesMul non-2 non-0 = refl
reducePreservesMul non-2 non-1 = refl
reducePreservesMul non-2 non-2 = refl
reducePreservesMul non-2 non-3 = refl
reducePreservesMul non-2 non-4 = refl
reducePreservesMul non-2 non-5 = refl
reducePreservesMul non-2 non-6 = refl
reducePreservesMul non-2 non-7 = refl
reducePreservesMul non-2 non-8 = refl
reducePreservesMul non-3 non-0 = refl
reducePreservesMul non-3 non-1 = refl
reducePreservesMul non-3 non-2 = refl
reducePreservesMul non-3 non-3 = refl
reducePreservesMul non-3 non-4 = refl
reducePreservesMul non-3 non-5 = refl
reducePreservesMul non-3 non-6 = refl
reducePreservesMul non-3 non-7 = refl
reducePreservesMul non-3 non-8 = refl
reducePreservesMul non-4 non-0 = refl
reducePreservesMul non-4 non-1 = refl
reducePreservesMul non-4 non-2 = refl
reducePreservesMul non-4 non-3 = refl
reducePreservesMul non-4 non-4 = refl
reducePreservesMul non-4 non-5 = refl
reducePreservesMul non-4 non-6 = refl
reducePreservesMul non-4 non-7 = refl
reducePreservesMul non-4 non-8 = refl
reducePreservesMul non-5 non-0 = refl
reducePreservesMul non-5 non-1 = refl
reducePreservesMul non-5 non-2 = refl
reducePreservesMul non-5 non-3 = refl
reducePreservesMul non-5 non-4 = refl
reducePreservesMul non-5 non-5 = refl
reducePreservesMul non-5 non-6 = refl
reducePreservesMul non-5 non-7 = refl
reducePreservesMul non-5 non-8 = refl
reducePreservesMul non-6 non-0 = refl
reducePreservesMul non-6 non-1 = refl
reducePreservesMul non-6 non-2 = refl
reducePreservesMul non-6 non-3 = refl
reducePreservesMul non-6 non-4 = refl
reducePreservesMul non-6 non-5 = refl
reducePreservesMul non-6 non-6 = refl
reducePreservesMul non-6 non-7 = refl
reducePreservesMul non-6 non-8 = refl
reducePreservesMul non-7 non-0 = refl
reducePreservesMul non-7 non-1 = refl
reducePreservesMul non-7 non-2 = refl
reducePreservesMul non-7 non-3 = refl
reducePreservesMul non-7 non-4 = refl
reducePreservesMul non-7 non-5 = refl
reducePreservesMul non-7 non-6 = refl
reducePreservesMul non-7 non-7 = refl
reducePreservesMul non-7 non-8 = refl
reducePreservesMul non-8 non-0 = refl
reducePreservesMul non-8 non-1 = refl
reducePreservesMul non-8 non-2 = refl
reducePreservesMul non-8 non-3 = refl
reducePreservesMul non-8 non-4 = refl
reducePreservesMul non-8 non-5 = refl
reducePreservesMul non-8 non-6 = refl
reducePreservesMul non-8 non-7 = refl
reducePreservesMul non-8 non-8 = refl

record NonaryTernaryRingReductionReceipt : Set where
  constructor nonaryTernaryRingReductionReceipt
  field
    reduction : NonaryTruth → TriTruth
    section : TriTruth → NonaryTruth
    sectionLaw : (x : TriTruth) → reduction (section x) ≡ x
    zeroLaw : reduction Z9.nonaryZero ≡ F3.triZero
    oneLaw : reduction Z9.nonaryOne ≡ F3.triOne
    addLaw :
      (a b : NonaryTruth) →
      reduction (Z9.nonaryAdd a b)
      ≡ F3.triAdd (reduction a) (reduction b)
    mulLaw :
      (a b : NonaryTruth) →
      reduction (Z9.nonaryMul a b)
      ≡ F3.triMul (reduction a) (reduction b)

open NonaryTernaryRingReductionReceipt public

canonicalNonaryTernaryRingReduction : NonaryTernaryRingReductionReceipt
canonicalNonaryTernaryRingReduction =
  nonaryTernaryRingReductionReceipt
    reduce9to3
    section3to9
    reduceSection
    reducePreservesZero
    reducePreservesOne
    reducePreservesAdd
    reducePreservesMul
