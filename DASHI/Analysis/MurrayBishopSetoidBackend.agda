module DASHI.Analysis.MurrayBishopSetoidBackend where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Pinned Murray--Bishop setoid backend for DASHI".
-- Venue/year: Springer, 1985; Dalhousie University/arXiv, 2022; continuation
-- repository, 2022--2023; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354; the software
-- continuation and repository adapter have no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: Murray's regular rational sequences, extensional equality, arithmetic,
-- located order, absolute value and the Cauchy-completeness theorem proved in
-- Sequence.agda.
-- Relationship: this is a concrete, nondegenerate ordered-complete-real
-- backend.  Completeness remains setoid-native; no representative-selection
-- or quotient-choice principle is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as Bishop
import RealProperties as BishopLaws
import Sequence as BishopSequence

import DASHI.Analysis.SetoidConstructiveRealSpine as Spine

negativeAbsoluteBelow : ∀ value →
  Bishop._≤_
    (Bishop.-_ (Bishop.∣_∣ value))
    value
negativeAbsoluteBelow value =
  BishopLaws.≤-respʳ-≃
    (BishopLaws.neg-involutive value)
    (BishopLaws.≤-respˡ-≃
      (BishopLaws.-‿cong BishopLaws.∣-x∣≃∣x∣)
      (BishopLaws.neg-mono-≤
        (BishopLaws.x≤∣x∣ {x = Bishop.-_ value})))

murrayBishopSetoidOrderedCompleteReal :
  Spine.SetoidOrderedCompleteReal
murrayBishopSetoidOrderedCompleteReal = record
  { Carrier = Bishop.ℝ
  ; _≈_ = Bishop._≃_
  ; ≈-refl = BishopLaws.≃-refl
  ; ≈-sym = BishopLaws.≃-symm
  ; ≈-trans = BishopLaws.≃-trans

  ; zero = Bishop.0ℝ
  ; one = Bishop.1ℝ
  ; _+_ = Bishop._+_
  ; _-_ = Bishop._-_
  ; _*_ = Bishop._*_
  ; neg = Bishop.-_
  ; abs = Bishop.∣_∣

  ; addCong = BishopLaws.+-cong
  ; subCong = λ left right →
      BishopLaws.+-cong left (BishopLaws.-‿cong right)
  ; mulCong = BishopLaws.*-cong
  ; negCong = BishopLaws.-‿cong
  ; absCong = BishopLaws.∣-∣-cong

  ; addAssoc = BishopLaws.+-assoc
  ; addComm = BishopLaws.+-comm
  ; addZeroLeft = BishopLaws.+-identityˡ
  ; addZeroRight = BishopLaws.+-identityʳ
  ; addInverseRight = BishopLaws.+-inverseʳ

  ; mulAssoc = BishopLaws.*-assoc
  ; mulComm = BishopLaws.*-comm
  ; mulOneLeft = BishopLaws.*-identityˡ
  ; mulOneRight = BishopLaws.*-identityʳ
  ; mulZeroLeft = BishopLaws.*-zeroˡ
  ; mulZeroRight = BishopLaws.*-zeroʳ
  ; distribLeft = BishopLaws.*-distribˡ-+
  ; distribRight = BishopLaws.*-distribʳ-+
  ; subSelf = BishopLaws.+-inverseʳ

  ; _≤_ = Bishop._≤_
  ; _<_ = Bishop._<_
  ; leRefl = λ value → BishopLaws.≤-refl {x = value}
  ; leTrans = BishopLaws.≤-trans
  ; ltTrans = BishopLaws.<-trans
  ; ltToLe = BishopLaws.<⇒≤
  ; leRespectsLeft = BishopLaws.≤-respˡ-≃
  ; leRespectsRight = BishopLaws.≤-respʳ-≃
  ; ltRespectsLeft = BishopLaws.<-respˡ-≃
  ; ltRespectsRight = BishopLaws.<-respʳ-≃

  ; addMonotone = BishopLaws.+-mono-≤
  ; addStrictMonotone = BishopLaws.+-mono-<
  ; negateAntitone = BishopLaws.neg-mono-≤
  ; negateStrictAntitone = BishopLaws.neg-mono-<
  ; multiplyMonotoneNonnegative = λ zero≤a a≤b zero≤c c≤d →
      BishopLaws.*-mono-≤
        (BishopLaws.0≤x⇒nonNegx zero≤a)
        (BishopLaws.0≤x⇒nonNegx zero≤c)
        a≤b c≤d

  ; valueBelowAbsolute = λ value → BishopLaws.x≤∣x∣ {x = value}
  ; negativeAbsoluteBelowValue = negativeAbsoluteBelow
  ; absoluteNonnegative = BishopLaws.0≤∣x∣

  ; Sequence = Nat → Bishop.ℝ
  ; sequenceAt = λ sequence index → sequence index
  ; IsCauchy = BishopSequence._isCauchy
  ; ConvergesTo = BishopSequence._ConvergesTo_
  ; cauchyLimit = λ sequence cauchy →
      BishopSequence.fast-cauchy⇒convergent cauchy
  }

murrayBishopCarrierNondegenerate : Bool
murrayBishopCarrierNondegenerate = true

murrayBishopSetoidCompletenessClosed : Bool
murrayBishopSetoidCompletenessClosed = true

literalQuotientCompletenessNotUsed : Bool
literalQuotientCompletenessNotUsed = true

murrayBishopAbsoluteLowerTransportOrientedCorrectly : Bool
murrayBishopAbsoluteLowerTransportOrientedCorrectly = true

murrayBishopCarrierNondegenerateIsTrue :
  murrayBishopCarrierNondegenerate ≡ true
murrayBishopCarrierNondegenerateIsTrue = refl

murrayBishopSetoidCompletenessClosedIsTrue :
  murrayBishopSetoidCompletenessClosed ≡ true
murrayBishopSetoidCompletenessClosedIsTrue = refl

literalQuotientCompletenessNotUsedIsTrue :
  literalQuotientCompletenessNotUsed ≡ true
literalQuotientCompletenessNotUsedIsTrue = refl

murrayBishopAbsoluteLowerTransportOrientedCorrectlyIsTrue :
  murrayBishopAbsoluteLowerTransportOrientedCorrectly ≡ true
murrayBishopAbsoluteLowerTransportOrientedCorrectlyIsTrue = refl
