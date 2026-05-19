module DASHI.Arithmetic.PrimeIndexedPressure where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_+_; _≤_)
open import Data.Product using (_×_; _,_)

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; normalizeAddCanonical
  ; primeProfile
  )
open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.CancellationPressureRefinement using
  ( RefinedCancellationPressure
  ; canonical⇒refinedBounded
  ; normalizeAdd⇒refinedBounded
  )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateSupportPressure )

PrimeContributionVec : Set
PrimeContributionVec = Vec15 Nat

sum15 : PrimeContributionVec → Nat
sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 + a3 + a5 + a7 + a11 + a13 + a17 + a19 + a23 + a29 + a31 + a41 + a47 + a59 + a71

canonicalZeroVec : PrimeContributionVec
canonicalZeroVec = mkVec15 zero zero zero zero zero zero zero zero zero zero zero zero zero zero zero

primeIndexedPressureAt : NormalizeAddState → PrimeContributionVec
primeIndexedPressureAt = primeProfile

postulate
  primeIndexedPressure-factor :
    ∀ s →
    sum15 (primeIndexedPressureAt s) ≡ RefinedCancellationPressure s

primeContribution : SSP → NormalizeAddState → Nat
primeContribution p s with primeIndexedPressureAt s | p
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p2  = a2
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p3  = a3
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p5  = a5
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p7  = a7
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p11 = a11
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p13 = a13
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p17 = a17
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p19 = a19
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p23 = a23
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p29 = a29
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p31 = a31
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p41 = a41
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p47 = a47
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p59 = a59
primeContribution p s | mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71 | p71 = a71

canonical⇒primeIndexedBounded :
  ∀ s →
  normalizeAddCanonical s →
  sum15 (primeIndexedPressureAt s) ≤ StateSupportPressure s
canonical⇒primeIndexedBounded s canon
  rewrite primeIndexedPressure-factor s
  = canonical⇒refinedBounded s canon

normalizeAdd⇒primeIndexedBounded :
  ∀ s →
  sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤
  StateSupportPressure (normalizeAdd s)
normalizeAdd⇒primeIndexedBounded s
  rewrite primeIndexedPressure-factor (normalizeAdd s)
  = normalizeAdd⇒refinedBounded s

normalizeAdd⇒primeIndexedCanonicalBounded :
  ∀ s →
  normalizeAddCanonical (normalizeAdd s) ×
  (sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤
   StateSupportPressure (normalizeAdd s))
normalizeAdd⇒primeIndexedCanonicalBounded s =
  normalizeAdd-canonical s , normalizeAdd⇒primeIndexedBounded s
