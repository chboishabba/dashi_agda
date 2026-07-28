module DASHI.Analysis.FastCauchyConstructedRealBackendExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Direct setoid backend for DASHI's pre-existing FastCauchyReal carrier.
--
-- This is deliberately separate from FastCauchyQuotientRealization: the direct
-- backend keeps extensional equality, while the older ConstructedOrderedCompleteReal
-- interface remains available through the explicit quotient seam.
------------------------------------------------------------------------

record FastCauchyBackendPackaging
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A) : Set₁ where
  field
    negRespect : ∀ {a b} → Fast._≈R_ a b →
      Fast._≈R_ (Fast.negR operations a) (Fast.negR operations b)

    absRespect : ∀ {a b} → Fast._≈R_ a b →
      Fast._≈R_ (Fast.absR operations a) (Fast.absR operations b)

    leResp : ∀ {a a′ b b′} →
      Fast._≈R_ a a′ → Fast._≈R_ b b′ →
      Fast.leR operations a b → Fast.leR operations a′ b′

    ltResp : ∀ {a a′ b b′} →
      Fast._≈R_ a a′ → Fast._≈R_ b b′ →
      Fast.ltR operations a b → Fast.ltR operations a′ b′

    orderedFieldLaws : Set

    Sequence : Set
    sequenceAt : Sequence → Nat → Fast.FastCauchyReal A
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Fast.FastCauchyReal A → Set
    cauchyLimit : (sequence : Sequence) → IsCauchy sequence →
      Σ (Fast.FastCauchyReal A) (λ limit → ConvergesTo sequence limit)
    limitUnique : ∀ {sequence left right} →
      ConvergesTo sequence left → ConvergesTo sequence right →
      Fast._≈R_ left right

    fromFunction : (Nat → Fast.FastCauchyReal A) → Sequence
    sequenceAtFromFunction : ∀ function index →
      Fast._≈R_ (sequenceAt (fromFunction function) index) (function index)

open FastCauchyBackendPackaging public

fastCauchySetoidOrderedCompleteReal :
  ∀ {A} (operations : Fast.FastCauchyOperations A) →
  FastCauchyBackendPackaging A operations →
  Spine.SetoidOrderedCompleteReal
fastCauchySetoidOrderedCompleteReal operations packaging = record
  { Carrier = Fast.FastCauchyReal _
  ; _≈_ = Fast._≈R_
  ; ≈-refl = Fast.reflexive (Fast.equalityLaws operations) _
  ; ≈-sym = Fast.symmetric (Fast.equalityLaws operations)
  ; ≈-trans = Fast.transitive (Fast.equalityLaws operations)
  ; zero = Fast.zeroR operations
  ; one = Fast.oneR operations
  ; _+_ = Fast.addR operations
  ; _-_ = Fast.subR operations
  ; _*_ = Fast.mulR operations
  ; neg = Fast.negR operations
  ; abs = Fast.absR operations
  ; _≤_ = Fast.leR operations
  ; _<_ = Fast.ltR operations
  ; addCong = Fast.addRespect operations
  ; subCong = Fast.subRespect operations
  ; mulCong = Fast.mulRespect operations
  ; negCong = negRespect packaging
  ; absCong = absRespect packaging
  ; leResp = leResp packaging
  ; ltResp = ltResp packaging
  ; orderedFieldLaws = orderedFieldLaws packaging
  ; Sequence = Sequence packaging
  ; sequenceAt = sequenceAt packaging
  ; IsCauchy = IsCauchy packaging
  ; ConvergesTo = ConvergesTo packaging
  ; cauchyLimit = cauchyLimit packaging
  ; limitUnique = limitUnique packaging
  }

fastCauchyFunctionSequenceRealization :
  ∀ {A} (operations : Fast.FastCauchyOperations A)
    (packaging : FastCauchyBackendPackaging A operations) →
  Spine.FunctionSequenceRealization
    (fastCauchySetoidOrderedCompleteReal operations packaging)
fastCauchyFunctionSequenceRealization operations packaging = record
  { fromFunction = fromFunction packaging
  ; sequenceAtFromFunction = sequenceAtFromFunction packaging
  }

fastCauchyConstructiveRealBackend :
  ∀ {A} (operations : Fast.FastCauchyOperations A) →
  FastCauchyBackendPackaging A operations →
  Spine.ConstructiveRealBackend
fastCauchyConstructiveRealBackend operations packaging = record
  { backendName = "DASHI quotient-free FastCauchyReal"
  ; real = fastCauchySetoidOrderedCompleteReal operations packaging
  ; functionSequences = fastCauchyFunctionSequenceRealization operations packaging
  ; quotientOptional = Fast.FastCauchyQuotientRealization _ operations
  }

fastCauchyCarrierAndEqualityLevel : ProofLevel
fastCauchyCarrierAndEqualityLevel = machineChecked

fastCauchyBackendPackagingLevel : ProofLevel
fastCauchyBackendPackagingLevel = conditional

fastCauchyBackendAssemblyLevel : ProofLevel
fastCauchyBackendAssemblyLevel = machineChecked
