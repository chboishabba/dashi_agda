module DASHI.Algebra.StageQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  ; rotateTri
  )
open import LogicTlurey using
  ( Stage
  ; seed ; counter ; resonance ; overflow
  ; next
  ; stageTone
  )
open import DASHI.Foundations.StageAtlasZeroToEleven using
  ( StageAtlasZeroToEleven
  ; StageAtlasRevolution
  ; StageAtlasZeroToElevenRow
  ; atlas-11
  ; rev-2
  ; canonicalStageAtlasZeroToElevenRows
  ; residue-of
  ; tone-of
  ; revolution-of
  ; tone-of-stage
  )

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

q : Stage → TriTruth
q = stageTone

q-surj-low : q seed ≡ tri-low
q-surj-low = refl

q-surj-mid : q counter ≡ tri-mid
q-surj-mid = refl

q-surj-high : q resonance ≡ tri-high
q-surj-high = refl

q-overflow-collapse : q overflow ≡ q seed
q-overflow-collapse = refl

q-next-seed :
  q (next seed) ≡ rotateTri (q seed)
q-next-seed = refl

q-next-counter :
  q (next counter) ≡ rotateTri (q counter)
q-next-counter = refl

q-next-resonance :
  q (next resonance) ≡ rotateTri (q resonance)
q-next-resonance = refl

q-next-overflow : q (next overflow) ≡ tri-low
q-next-overflow = refl

rotate-q-overflow : rotateTri (q overflow) ≡ tri-mid
rotate-q-overflow = refl

overflow-equivariance-fails :
  q (next overflow) ≢ rotateTri (q overflow)
overflow-equivariance-fails ()

record StageQuotientSeam : Set where
  constructor stageQuotientSeam
  field
    quotient : Stage → TriTruth
    representative-low : quotient seed ≡ tri-low
    representative-mid : quotient counter ≡ tri-mid
    representative-high : quotient resonance ≡ tri-high
    overflow-collapse : quotient overflow ≡ quotient seed
    seed-equivariant :
      quotient (next seed) ≡ rotateTri (quotient seed)
    counter-equivariant :
      quotient (next counter) ≡ rotateTri (quotient counter)
    resonance-equivariant :
      quotient (next resonance) ≡ rotateTri (quotient resonance)
    overflow-seam :
      quotient (next overflow) ≢ rotateTri (quotient overflow)

record Stage12FibreSurface : Set where
  constructor mkStage12FibreSurface
  field
    atlasRows : List StageAtlasZeroToElevenRow
    atlasRowsAreCanonical :
      atlasRows ≡ canonicalStageAtlasZeroToElevenRows
    residue : StageAtlasZeroToEleven → Stage
    quotient : StageAtlasZeroToEleven → TriTruth
    carry-depth : StageAtlasZeroToEleven → StageAtlasRevolution
    fibre-of-quotient :
      ∀ c →
      quotient c ≡ stageTone (residue c)
    carry-depth-matches :
      ∀ c →
      carry-depth c ≡ revolution-of c
    seam :
      quotient atlas-11 ≡ tri-low
    carry-depth-seam :
      carry-depth atlas-11 ≡ rev-2
    successor-non-equivariant :
      quotient atlas-11 ≢ rotateTri (quotient atlas-11)

canonicalStage12FibreSurface : Stage12FibreSurface
canonicalStage12FibreSurface =
  mkStage12FibreSurface
    canonicalStageAtlasZeroToElevenRows
    refl
    residue-of
    tone-of
    revolution-of
    tone-of-stage
    (λ c → refl)
    refl
    refl
    (λ ())

stageQuotientSeamSurface : StageQuotientSeam
stageQuotientSeamSurface =
  stageQuotientSeam
    q
    q-surj-low
    q-surj-mid
    q-surj-high
    q-overflow-collapse
    q-next-seed
    q-next-counter
    q-next-resonance
    overflow-equivariance-fails
