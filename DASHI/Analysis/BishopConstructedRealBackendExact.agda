module DASHI.Analysis.BishopConstructedRealBackendExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete Bishop backend for DASHI's setoid-aware real contract.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354.  No DOI was assigned to the thesis.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 582c6afcdf805d06730c8c0aa970f4a6e033b611.
--
-- The carrier, equality, sequence semantics, completeness and uniqueness below
-- are the imported checked objects.  Algebra/order packaging is a separate
-- record because the Bishop library and DASHI expose differently shaped bundles.
------------------------------------------------------------------------

Bishopℝ : Set
Bishopℝ = BishopReal.ℝ

record BishopAlgebraOrderPackaging : Set₁ where
  field
    addCong : ∀ {a a′ b b′ : Bishopℝ} →
      BishopReal._≃_ a a′ → BishopReal._≃_ b b′ →
      BishopReal._≃_ (BishopReal._+_ a b) (BishopReal._+_ a′ b′)

    subCong : ∀ {a a′ b b′ : Bishopℝ} →
      BishopReal._≃_ a a′ → BishopReal._≃_ b b′ →
      BishopReal._≃_ (BishopReal._-_ a b) (BishopReal._-_ a′ b′)

    mulCong : ∀ {a a′ b b′ : Bishopℝ} →
      BishopReal._≃_ a a′ → BishopReal._≃_ b b′ →
      BishopReal._≃_ (BishopReal._*_ a b) (BishopReal._*_ a′ b′)

    negCong : ∀ {a b : Bishopℝ} →
      BishopReal._≃_ a b → BishopReal._≃_ (BishopReal.-_ a) (BishopReal.-_ b)

    absCong : ∀ {a b : Bishopℝ} →
      BishopReal._≃_ a b → BishopReal._≃_ (BishopReal.∣_∣ a) (BishopReal.∣_∣ b)

    leResp : ∀ {a a′ b b′ : Bishopℝ} →
      BishopReal._≃_ a a′ → BishopReal._≃_ b b′ →
      BishopReal._≤_ a b → BishopReal._≤_ a′ b′

    ltResp : ∀ {a a′ b b′ : Bishopℝ} →
      BishopReal._≃_ a a′ → BishopReal._≃_ b b′ →
      BishopReal._<_ a b → BishopReal._<_ a′ b′

    orderedFieldLaws : Set

open BishopAlgebraOrderPackaging public

bishopSetoidOrderedCompleteReal :
  BishopAlgebraOrderPackaging → Spine.SetoidOrderedCompleteReal
bishopSetoidOrderedCompleteReal packaging = record
  { Carrier = Bishopℝ
  ; _≈_ = BishopReal._≃_
  ; ≈-refl = BishopProperties.≃-refl
  ; ≈-sym = BishopProperties.≃-symm
  ; ≈-trans = BishopProperties.≃-trans
  ; zero = BishopReal.0ℝ
  ; one = BishopReal.1ℝ
  ; _+_ = BishopReal._+_
  ; _-_ = BishopReal._-_
  ; _*_ = BishopReal._*_
  ; neg = BishopReal.-_
  ; abs = BishopReal.∣_∣
  ; _≤_ = BishopReal._≤_
  ; _<_ = BishopReal._<_
  ; addCong = addCong packaging
  ; subCong = subCong packaging
  ; mulCong = mulCong packaging
  ; negCong = negCong packaging
  ; absCong = absCong packaging
  ; leResp = leResp packaging
  ; ltResp = ltResp packaging
  ; orderedFieldLaws = orderedFieldLaws packaging
  ; Sequence = Nat → Bishopℝ
  ; sequenceAt = λ sequence index → sequence index
  ; IsCauchy = BishopSequence._isCauchy
  ; ConvergesTo = BishopSequence._ConvergesTo_
  ; cauchyLimit = λ sequence cauchy → BishopSequence.fast-cauchy⇒convergent cauchy
  ; limitUnique = BishopSequence.uniqueness-of-limits
  }

bishopFunctionSequenceRealization :
  (packaging : BishopAlgebraOrderPackaging) →
  Spine.FunctionSequenceRealization (bishopSetoidOrderedCompleteReal packaging)
bishopFunctionSequenceRealization packaging = record
  { fromFunction = λ sequence → sequence
  ; sequenceAtFromFunction = λ sequence index → BishopProperties.≃-refl
  }

bishopConstructiveRealBackend :
  BishopAlgebraOrderPackaging → Spine.ConstructiveRealBackend
bishopConstructiveRealBackend packaging = record
  { backendName = "viktorcsimma/bishop regular rational-sequence reals"
  ; real = bishopSetoidOrderedCompleteReal packaging
  ; functionSequences = bishopFunctionSequenceRealization packaging
  ; quotientOptional = Set
  }

record BishopBackendReceipt
    (packaging : BishopAlgebraOrderPackaging) : Set₁ where
  field
    backend : Spine.ConstructiveRealBackend
    backendExact : backend ≡ bishopConstructiveRealBackend packaging
    equalityIsBishopSetoid : Set
    completenessIsImportedBishopTheorem : Set
    noPropositionalEqualityIdentification : Set

open BishopBackendReceipt public

bishopCarrierEqualityCompletenessLevel : ProofLevel
bishopCarrierEqualityCompletenessLevel = machineChecked

bishopAlgebraOrderPackagingLevel : ProofLevel
bishopAlgebraOrderPackagingLevel = conditional

bishopBackendAssemblyLevel : ProofLevel
bishopBackendAssemblyLevel = machineChecked
