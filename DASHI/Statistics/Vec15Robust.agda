module DASHI.Statistics.Vec15Robust where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_∸_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties as NatP using (_≤?_; ≤-refl; n∸n≡0; +-identityʳ)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Statistics.Vec15Descriptive using
  ( PrimeCarrier15
  ; sum15
  ; max15
  ; min15
  ; maxNat
  ; minNat
  ; range15
  ; countNonZero15
  ; median15
  ; lowerQuartile15
  ; upperQuartile15
  ; rank15
  )

open import DASHI.Statistics.Vec15Order using
  ( selectMask15
  ; map15
  ; clampNat
  ; absDiffNat
  ; sortAsc
  ; toList15
  )

------------------------------------------------------------------------
-- Robust/outlier surface for the 15-prime carrier.
--
-- The concrete part now covers:
--   - IQR-based fences
--   - Tukey and Hampel masks
--   - winsorization
--   - trimmed mean on the sorted middle block
--   - median absolute deviation
--
-- Summary surfaces stay explicit but are now backed by real operators.

constant15 : Nat → PrimeCarrier15
constant15 n =
  mkVec15 n n n n n n n n n n n n n n n

maxNat-self : ∀ n → maxNat n n ≡ n
maxNat-self zero = refl
maxNat-self (suc n) rewrite maxNat-self n = refl

minNat-self : ∀ n → minNat n n ≡ n
minNat-self zero = refl
minNat-self (suc n) rewrite minNat-self n = refl

iqr15 : PrimeCarrier15 → Nat
iqr15 v = upperQuartile15 v ∸ lowerQuartile15 v

record TukeyFence15 : Set where
  constructor fence15
  field
    lowerFence15 : Nat
    upperFence15 : Nat

-- A lightweight Tukey-style fence based on the IQR.
tukeyFence15 : PrimeCarrier15 → TukeyFence15
tukeyFence15 v =
  fence15
    (lowerQuartile15 v ∸ iqr15 v)
    (upperQuartile15 v + iqr15 v)

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

leqNatBool : Nat → Nat → Bool
leqNatBool x y with x NatP.≤? y
... | yes _ = true
... | no _ = false

outsideFenceMask15 : Nat → Nat → PrimeCarrier15 → Vec15 Bool
outsideFenceMask15 lo hi (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  mkVec15
    (notBool (andBool (leqNatBool lo a2) (leqNatBool a2 hi)))
    (notBool (andBool (leqNatBool lo a3) (leqNatBool a3 hi)))
    (notBool (andBool (leqNatBool lo a5) (leqNatBool a5 hi)))
    (notBool (andBool (leqNatBool lo a7) (leqNatBool a7 hi)))
    (notBool (andBool (leqNatBool lo a11) (leqNatBool a11 hi)))
    (notBool (andBool (leqNatBool lo a13) (leqNatBool a13 hi)))
    (notBool (andBool (leqNatBool lo a17) (leqNatBool a17 hi)))
    (notBool (andBool (leqNatBool lo a19) (leqNatBool a19 hi)))
    (notBool (andBool (leqNatBool lo a23) (leqNatBool a23 hi)))
    (notBool (andBool (leqNatBool lo a29) (leqNatBool a29 hi)))
    (notBool (andBool (leqNatBool lo a31) (leqNatBool a31 hi)))
    (notBool (andBool (leqNatBool lo a41) (leqNatBool a41 hi)))
    (notBool (andBool (leqNatBool lo a47) (leqNatBool a47 hi)))
    (notBool (andBool (leqNatBool lo a59) (leqNatBool a59 hi)))
    (notBool (andBool (leqNatBool lo a71) (leqNatBool a71 hi)))

mad15 : PrimeCarrier15 → Nat
mad15 v = median15 (map15 (absDiffNat (median15 v)) v)

tukeyOutlierMask15 : PrimeCarrier15 → Vec15 Bool
tukeyOutlierMask15 v with tukeyFence15 v
... | fence15 lo hi = outsideFenceMask15 lo hi v

-- The Hampel fence is centered on the median and scaled by 3 * MAD.
hampelOutlierMask15 : PrimeCarrier15 → Vec15 Bool
hampelOutlierMask15 v =
  outsideFenceMask15
    (median15 v ∸ 3 * mad15 v)
    (median15 v + 3 * mad15 v)
    v

winsorize15 : PrimeCarrier15 → PrimeCarrier15
winsorize15 v with tukeyFence15 v
... | fence15 lo hi = map15 (clampNat lo hi) v

middle11Sum : List Nat → Nat
middle11Sum (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ []) =
  x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13
middle11Sum _ = zero

trimmedMean15 : PrimeCarrier15 → Nat
trimmedMean15 v = middle11Sum (sortAsc (toList15 v)) / 11

{-
------------------------------------------------------------------------
-- Small constructive sanity lemmas on a constant carrier.

max15-constant : ∀ n → max15 (constant15 n) ≡ n
max15-constant n
  rewrite maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
        | maxNat-self n
  = refl

min15-constant : ∀ n → min15 (constant15 n) ≡ n
min15-constant n
  rewrite minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
        | minNat-self n
  = refl

lowerQuartile15-constant : ∀ n → lowerQuartile15 (constant15 n) ≡ n
lowerQuartile15-constant n = refl

median15-constant : ∀ n → median15 (constant15 n) ≡ n
median15-constant n = refl

upperQuartile15-constant : ∀ n → upperQuartile15 (constant15 n) ≡ n
upperQuartile15-constant n = refl

range15-constant-zero : ∀ n → range15 (constant15 n) ≡ zero
range15-constant-zero n
  rewrite max15-constant n
        | min15-constant n
        | n∸n≡0 n
  = refl

absDiffNat-self : ∀ n → absDiffNat n n ≡ zero
absDiffNat-self n with n NatP.≤? n
... | yes _ rewrite n∸n≡0 n = refl
... | no n≰n = ⊥-elim (n≰n ≤-refl)

tukeyFence15-constant : ∀ n → tukeyFence15 (constant15 n) ≡ fence15 n n
tukeyFence15-constant n
  rewrite lowerQuartile15-constant n
        | upperQuartile15-constant n
        | n∸n≡0 n
        | +-identityʳ n
  = refl

winsorize15-constant : ∀ n → winsorize15 (constant15 n) ≡ constant15 n
winsorize15-constant n
  rewrite tukeyFence15-constant n
  = refl

mad15-constant-zero : ∀ n → mad15 (constant15 n) ≡ zero
mad15-constant-zero n
  rewrite median15-constant n
        | absDiffNat-self n
  = refl
-}

------------------------------------------------------------------------
-- Honest robust summaries.
--
-- These summary values are now concrete aliases over the real operators.

tukeySummary15 : PrimeCarrier15 → Nat
tukeySummary15 = range15

hampelSummary15 : PrimeCarrier15 → Nat
hampelSummary15 = mad15

winsorizedSummary15 : PrimeCarrier15 → Nat
winsorizedSummary15 v = sum15 (winsorize15 v)

zeroCarrier15 : PrimeCarrier15
zeroCarrier15 = mkVec15 zero zero zero zero zero zero zero zero zero zero zero zero zero zero zero

selectMask15-zeroCarrier : ∀ threshold →
  selectMask15 threshold zeroCarrier15 ≡
  mkVec15 true true true true true true true true true true true true true true true
selectMask15-zeroCarrier threshold = refl

rank15-zeroCarrier : ∀ threshold → rank15 threshold zeroCarrier15 ≡ 15
rank15-zeroCarrier threshold = refl

countNonZero15-zeroCarrier : countNonZero15 zeroCarrier15 ≡ zero
countNonZero15-zeroCarrier = refl

tukeyOutlierMask15-zeroCarrier : tukeyOutlierMask15 zeroCarrier15 ≡
  mkVec15 false false false false false false false false false false false false false false false
tukeyOutlierMask15-zeroCarrier = refl

hampelOutlierMask15-zeroCarrier : hampelOutlierMask15 zeroCarrier15 ≡
  mkVec15 false false false false false false false false false false false false false false false
hampelOutlierMask15-zeroCarrier = refl

winsorize15-zeroCarrier : winsorize15 zeroCarrier15 ≡ zeroCarrier15
winsorize15-zeroCarrier = refl

mad15-zeroCarrier : mad15 zeroCarrier15 ≡ zero
mad15-zeroCarrier = refl

tukeySummary15-zeroCarrier : tukeySummary15 zeroCarrier15 ≡ zero
tukeySummary15-zeroCarrier = refl

hampelSummary15-zeroCarrier : hampelSummary15 zeroCarrier15 ≡ zero
hampelSummary15-zeroCarrier = refl

winsorizedSummary15-zeroCarrier : winsorizedSummary15 zeroCarrier15 ≡ zero
winsorizedSummary15-zeroCarrier = refl
