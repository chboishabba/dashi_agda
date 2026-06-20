module DASHI.Foundations.StageAtlasZeroToEleven where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import LogicTlurey using (Stage; seed; counter; resonance; overflow; stageTone)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : ∀ {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Carrier and coordinates.
------------------------------------------------------------------------

data StageAtlasZeroToEleven : Set where
  atlas-0 : StageAtlasZeroToEleven
  atlas-1 : StageAtlasZeroToEleven
  atlas-2 : StageAtlasZeroToEleven
  atlas-3 : StageAtlasZeroToEleven
  atlas-4 : StageAtlasZeroToEleven
  atlas-5 : StageAtlasZeroToEleven
  atlas-6 : StageAtlasZeroToEleven
  atlas-7 : StageAtlasZeroToEleven
  atlas-8 : StageAtlasZeroToEleven
  atlas-9 : StageAtlasZeroToEleven
  atlas-10 : StageAtlasZeroToEleven
  atlas-11 : StageAtlasZeroToEleven

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

five : Nat
five = suc four

six : Nat
six = suc five

seven : Nat
seven = suc six

eight : Nat
eight = suc seven

nine : Nat
nine = suc eight

ten : Nat
ten = suc nine

eleven : Nat
eleven = suc ten

twelve : Nat
twelve = suc eleven

carrierSize : Nat
carrierSize = twelve

carrierSizeIsTwelve : carrierSize ≡ twelve
carrierSizeIsTwelve = refl

toNat : StageAtlasZeroToEleven → Nat
toNat atlas-0 = zero
toNat atlas-1 = one
toNat atlas-2 = two
toNat atlas-3 = three
toNat atlas-4 = four
toNat atlas-5 = five
toNat atlas-6 = six
toNat atlas-7 = seven
toNat atlas-8 = eight
toNat atlas-9 = nine
toNat atlas-10 = ten
toNat atlas-11 = eleven

data StageAtlasRevolution : Set where
  rev-0 : StageAtlasRevolution
  rev-1 : StageAtlasRevolution
  rev-2 : StageAtlasRevolution

rev-0≢rev-1 : rev-0 ≢ rev-1
rev-0≢rev-1 ()

rev-0≢rev-2 : rev-0 ≢ rev-2
rev-0≢rev-2 ()

rev-1≢rev-2 : rev-1 ≢ rev-2
rev-1≢rev-2 ()

rev-2≢rev-0 : rev-2 ≢ rev-0
rev-2≢rev-0 h = rev-0≢rev-2 (sym h)

revolution-of : StageAtlasZeroToEleven → StageAtlasRevolution
revolution-of atlas-0 = rev-0
revolution-of atlas-1 = rev-0
revolution-of atlas-2 = rev-0
revolution-of atlas-3 = rev-0
revolution-of atlas-4 = rev-1
revolution-of atlas-5 = rev-1
revolution-of atlas-6 = rev-1
revolution-of atlas-7 = rev-1
revolution-of atlas-8 = rev-2
revolution-of atlas-9 = rev-2
revolution-of atlas-10 = rev-2
revolution-of atlas-11 = rev-2

revolution-of-2 : revolution-of atlas-2 ≡ rev-0
revolution-of-2 = refl

revolution-of-11 : revolution-of atlas-11 ≡ rev-2
revolution-of-11 = refl

residue-of : StageAtlasZeroToEleven → Stage
residue-of atlas-0 = seed
residue-of atlas-1 = counter
residue-of atlas-2 = resonance
residue-of atlas-3 = overflow
residue-of atlas-4 = seed
residue-of atlas-5 = counter
residue-of atlas-6 = resonance
residue-of atlas-7 = overflow
residue-of atlas-8 = seed
residue-of atlas-9 = counter
residue-of atlas-10 = resonance
residue-of atlas-11 = overflow

tone-of : StageAtlasZeroToEleven → TriTruth
tone-of atlas-0 = tri-low
tone-of atlas-1 = tri-mid
tone-of atlas-2 = tri-high
tone-of atlas-3 = tri-low
tone-of atlas-4 = tri-low
tone-of atlas-5 = tri-mid
tone-of atlas-6 = tri-high
tone-of atlas-7 = tri-low
tone-of atlas-8 = tri-low
tone-of atlas-9 = tri-mid
tone-of atlas-10 = tri-high
tone-of atlas-11 = tri-low

tone-of-stage : (c : StageAtlasZeroToEleven) → tone-of c ≡ stageTone (residue-of c)
tone-of-stage atlas-0 = refl
tone-of-stage atlas-1 = refl
tone-of-stage atlas-2 = refl
tone-of-stage atlas-3 = refl
tone-of-stage atlas-4 = refl
tone-of-stage atlas-5 = refl
tone-of-stage atlas-6 = refl
tone-of-stage atlas-7 = refl
tone-of-stage atlas-8 = refl
tone-of-stage atlas-9 = refl
tone-of-stage atlas-10 = refl
tone-of-stage atlas-11 = refl

record StageAtlasTopologicalReading : Set where
  constructor topological-reading
  field
    residue : Stage
    revolution : StageAtlasRevolution

open StageAtlasTopologicalReading

topological-reading-of : StageAtlasZeroToEleven → StageAtlasTopologicalReading
topological-reading-of c =
  topological-reading (residue-of c) (revolution-of c)

data StageAtlasRowLabel : Set where
  seed-r0 : StageAtlasRowLabel
  counter-r0 : StageAtlasRowLabel
  resonance-r0 : StageAtlasRowLabel
  overflow-r0 : StageAtlasRowLabel
  seed-r1 : StageAtlasRowLabel
  counter-r1 : StageAtlasRowLabel
  resonance-r1 : StageAtlasRowLabel
  overflow-r1 : StageAtlasRowLabel
  seed-r2 : StageAtlasRowLabel
  counter-r2 : StageAtlasRowLabel
  resonance-r2 : StageAtlasRowLabel
  overflow-r2 : StageAtlasRowLabel

record StageAtlasZeroToElevenRow : Set where
  constructor atlas-row
  field
    coordinate : StageAtlasZeroToEleven
    coordinate-index : Nat
    coordinate-label : StageAtlasRowLabel
    residue : Stage
    revolution : StageAtlasRevolution
    tone : TriTruth
    coordinate-index-matches :
      coordinate-index ≡ toNat coordinate
    residue-matches :
      residue ≡ residue-of coordinate
    revolution-matches :
      revolution ≡ revolution-of coordinate
    tone-matches :
      tone ≡ stageTone residue

mk-row :
  (c : StageAtlasZeroToEleven) →
  (l : StageAtlasRowLabel) →
  StageAtlasZeroToElevenRow
mk-row c l =
  atlas-row
    c
    (toNat c)
    l
    (residue-of c)
    (revolution-of c)
    (tone-of c)
    refl
    refl
    refl
    (tone-of-stage c)

atlas-row-0 : StageAtlasZeroToElevenRow
atlas-row-0 = mk-row atlas-0 seed-r0

atlas-row-1 : StageAtlasZeroToElevenRow
atlas-row-1 = mk-row atlas-1 counter-r0

atlas-row-2 : StageAtlasZeroToElevenRow
atlas-row-2 = mk-row atlas-2 resonance-r0

atlas-row-3 : StageAtlasZeroToElevenRow
atlas-row-3 = mk-row atlas-3 overflow-r0

atlas-row-4 : StageAtlasZeroToElevenRow
atlas-row-4 = mk-row atlas-4 seed-r1

atlas-row-5 : StageAtlasZeroToElevenRow
atlas-row-5 = mk-row atlas-5 counter-r1

atlas-row-6 : StageAtlasZeroToElevenRow
atlas-row-6 = mk-row atlas-6 resonance-r1

atlas-row-7 : StageAtlasZeroToElevenRow
atlas-row-7 = mk-row atlas-7 overflow-r1

atlas-row-8 : StageAtlasZeroToElevenRow
atlas-row-8 = mk-row atlas-8 seed-r2

atlas-row-9 : StageAtlasZeroToElevenRow
atlas-row-9 = mk-row atlas-9 counter-r2

atlas-row-10 : StageAtlasZeroToElevenRow
atlas-row-10 = mk-row atlas-10 resonance-r2

atlas-row-11 : StageAtlasZeroToElevenRow
atlas-row-11 = mk-row atlas-11 overflow-r2

canonicalStageAtlasZeroToElevenRows : List StageAtlasZeroToElevenRow
canonicalStageAtlasZeroToElevenRows =
  atlas-row-0
  ∷ atlas-row-1
  ∷ atlas-row-2
  ∷ atlas-row-3
  ∷ atlas-row-4
  ∷ atlas-row-5
  ∷ atlas-row-6
  ∷ atlas-row-7
  ∷ atlas-row-8
  ∷ atlas-row-9
  ∷ atlas-row-10
  ∷ atlas-row-11
  ∷ []

canonicalStageAtlasZeroToElevenRowCount : Nat
canonicalStageAtlasZeroToElevenRowCount = twelve

canonicalStageAtlasZeroToElevenRowCountIs12 : canonicalStageAtlasZeroToElevenRowCount ≡ twelve
canonicalStageAtlasZeroToElevenRowCountIs12 = refl

record StageAtlasZeroToElevenNonPromotionSurface : Set where
  constructor atlas-nonpromotion-surface
  field
    atlasRows : List StageAtlasZeroToElevenRow
    atlasRowsAreCanonical : atlasRows ≡ canonicalStageAtlasZeroToElevenRows
    atlasSize : Nat
    atlasSizeIsCarrierSize : atlasSize ≡ carrierSize
    nonPromotionNarrativeLabel : Bool
    nonPromotionNarrativeLabelIsTrue : nonPromotionNarrativeLabel ≡ true
    nonPromotionAbsolutePhase : Bool
    nonPromotionAbsolutePhaseIsTrue : nonPromotionAbsolutePhase ≡ true
    nonPromotionSocialInference : Bool
    nonPromotionSocialInferenceIsTrue : nonPromotionSocialInference ≡ true

canonicalStageAtlasZeroToElevenNonPromotionSurface :
  StageAtlasZeroToElevenNonPromotionSurface
canonicalStageAtlasZeroToElevenNonPromotionSurface =
  atlas-nonpromotion-surface
    canonicalStageAtlasZeroToElevenRows
    refl
    carrierSize
    refl
    true
    refl
    true
    refl
    true
    refl

-- Topological compactness: shared residue with different revolutions.

topology-of-10 : topological-reading-of atlas-10 ≡ topological-reading resonance rev-2
topology-of-10 = refl

topology-of-2 : topological-reading-of atlas-2 ≡ topological-reading resonance rev-0
topology-of-2 = refl

topology-of-10-distinct-from-2 : topological-reading-of atlas-10 ≢ topological-reading-of atlas-2
topology-of-10-distinct-from-2 h =
  rev-2≢rev-0
    (cong StageAtlasTopologicalReading.revolution h)

topology-of-11 : topological-reading-of atlas-11 ≡ topological-reading overflow rev-2
topology-of-11 = refl

topology-of-1 : topological-reading-of atlas-1 ≡ topological-reading counter rev-0
topology-of-1 = refl

topology-of-11-distinct-from-1 : topological-reading-of atlas-11 ≢ topological-reading-of atlas-1
topology-of-11-distinct-from-1 h =
  rev-2≢rev-0
    (cong StageAtlasTopologicalReading.revolution h)
