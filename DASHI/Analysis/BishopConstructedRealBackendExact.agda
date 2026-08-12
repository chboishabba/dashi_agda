module DASHI.Analysis.BishopConstructedRealBackendExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete Bishop backend for DASHI's setoid-aware real contract.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI was assigned to the thesis.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- DASHI CONTRIBUTION
--
-- The carrier, extensional equality, arithmetic, order, sequence semantics,
-- completeness and uniqueness are now all connected to imported checked
-- Bishop objects.  The old packaging record remains as a reusable adapter, but
-- its concrete instance is no longer conditional: congruence of +,-,*,neg,abs
-- and transport of <=,< are assembled directly from RealProperties.
--
-- `orderedFieldLaws` in the legacy setoid spine is only an opaque Set marker;
-- the actual laws used by DASHI are the explicit RealProperties theorems wired
-- below (and the stronger MurrayBishopSetoidBackend record).  We therefore fill
-- that marker by the canonical inhabited type, without postulating any law.
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

bishopImportedAlgebraOrderPackaging : BishopAlgebraOrderPackaging
bishopImportedAlgebraOrderPackaging = record
  { addCong = BishopProperties.+-cong
  ; subCong = λ left right →
      BishopProperties.+-cong left (BishopProperties.-‿cong right)
  ; mulCong = BishopProperties.*-cong
  ; negCong = BishopProperties.-‿cong
  ; absCong = BishopProperties.∣-∣-cong
  ; leResp = λ left right proof →
      BishopProperties.≤-respʳ-≃ right
        (BishopProperties.≤-respˡ-≃ left proof)
  ; ltResp = λ left right proof →
      BishopProperties.<-respʳ-≃ right
        (BishopProperties.<-respˡ-≃ left proof)
  ; orderedFieldLaws = ⊤
  }

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

bishopImportedSetoidOrderedCompleteReal : Spine.SetoidOrderedCompleteReal
bishopImportedSetoidOrderedCompleteReal =
  bishopSetoidOrderedCompleteReal bishopImportedAlgebraOrderPackaging

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
  ; quotientOptional = ⊤
  }

bishopImportedConstructiveRealBackend : Spine.ConstructiveRealBackend
bishopImportedConstructiveRealBackend =
  bishopConstructiveRealBackend bishopImportedAlgebraOrderPackaging

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
bishopAlgebraOrderPackagingLevel = machineChecked

bishopBackendAssemblyLevel : ProofLevel
bishopBackendAssemblyLevel = machineChecked
