module DASHI.Physics.YangMills.BalabanClayT2QuaternionTailCollarClosureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as Quaternion
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact finite collar witness and transcendental normalization cutset.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354. No DOI was assigned.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = fzero ∷ mapList fsuc (allFin n)

lengthMap : ∀ {A B : Set} (f : A → B) xs →
  length (mapList f xs) ≡ length xs
lengthMap f [] = refl
lengthMap f (x ∷ xs) rewrite lengthMap f xs = refl

lengthAllFin : ∀ n → length (allFin n) ≡ n
lengthAllFin zero = refl
lengthAllFin (suc n) rewrite lengthMap fsuc (allFin n) | lengthAllFin n = refl

≤-reflN : ∀ n → n ≤ n
≤-reflN zero = z≤n
≤-reflN (suc n) = s≤s (≤-reflN n)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y} → x ≡ y → P x → P y
subst P refl px = px

record PhysicalPlaquetteCollarSlots (Block Plaquette : Set) : Set₁ where
  field
    slotPlaquette : Block → Fin 96 → Plaquette
    everyPhysicalChargedPlaquetteHasSlot : ∀ block plaquette → Set
    collarGeometryComplete : Set
    duplicateSlotsAllowedAsSafeOvercount : Set

open PhysicalPlaquetteCollarSlots public

chargedPlaquettes :
  ∀ {Block Plaquette} →
  PhysicalPlaquetteCollarSlots Block Plaquette → Block → List Plaquette
chargedPlaquettes slots block =
  mapList (slotPlaquette slots block) (allFin 96)

chargedPlaquettesLengthExact :
  ∀ {Block Plaquette}
    (slots : PhysicalPlaquetteCollarSlots Block Plaquette) block →
  length (chargedPlaquettes slots block) ≡ 96
chargedPlaquettesLengthExact slots block =
  let mapped = lengthMap (slotPlaquette slots block) (allFin 96)
      finite = lengthAllFin 96
  in trans mapped finite
  where
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl yz = yz

chargedPlaquettesCountAtMost96 :
  ∀ {Block Plaquette}
    (slots : PhysicalPlaquetteCollarSlots Block Plaquette) block →
  length (chargedPlaquettes slots block) ≤ 96
chargedPlaquettesCountAtMost96 slots block =
  subst (λ count → count ≤ 96)
    (sym (chargedPlaquettesLengthExact slots block))
    (≤-reflN 96)

------------------------------------------------------------------------
-- Bishop Taylor tails feed the exact SU(2) exponential and local logarithm.
------------------------------------------------------------------------

record BishopQuaternionTranscendentalClosure
    (series : Series.BishopElementaryPowerSeriesData)
    (exponential : Quaternion.BishopSU2ExponentialJetData series)
    (logarithm : Quaternion.BishopQuaternionLogData series) : Set₁ where
  field
    sineConfiguredAlternatingTail : Set
    cosineConfiguredAlternatingTail : Set
    scalarRemainderQuarticLiteral : ∀ value →
      Quaternion.scalarRemainderQuarticBound exponential value
    vectorRemainderCubicLiteral : ∀ value →
      Quaternion.vectorRemainderCubicBound exponential value

    logChartScalarPositive : ∀ quaternion →
      Quaternion.InLogChart logarithm quaternion → Set
    arcsinOverXAbsoluteConvergenceLiteral : ∀ point →
      Quaternion.arcsinOverXAbsoluteConvergence logarithm point
    arcsinOverXQuadraticRemainderLiteral : ∀ point →
      Quaternion.arcsinOverXQuadraticRemainder logarithm point

    fourFactorProductTelescopingNormBound : Set
    exactProductMinusGeneratedJetCubic : Set
    exactLogMinusGeneratedJetCubic : Set

open BishopQuaternionTranscendentalClosure public

record LiteralQuaternionNormalizationClosure
    (series : Series.BishopElementaryPowerSeriesData)
    (exponential : Quaternion.BishopSU2ExponentialJetData series)
    (logarithm : Quaternion.BishopQuaternionLogData series)
    (Block Plaquette : Set) : Set₁ where
  field
    transcendental :
      BishopQuaternionTranscendentalClosure series exponential logarithm
    collarSlots : PhysicalPlaquetteCollarSlots Block Plaquette
    normalization :
      Quaternion.GeneratedQuaternionNormalizationData
        series exponential logarithm Plaquette Block

    normalizationUsesGeneratedSlots : ∀ block →
      Quaternion.chargedPlaquettes normalization block
      ≡ chargedPlaquettes collarSlots block

open LiteralQuaternionNormalizationClosure public

collarSlotEnumerationLevel : ProofLevel
collarSlotEnumerationLevel = machineChecked

collarCountAtMost96Level : ProofLevel
collarCountAtMost96Level = machineChecked

quaternionTranscendentalInputsLevel : ProofLevel
quaternionTranscendentalInputsLevel = conditional

physicalCollarRealizationInputsLevel : ProofLevel
physicalCollarRealizationInputsLevel = conditional
