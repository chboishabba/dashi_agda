module DASHI.Analysis.RiemannG2CanonicalHXToHTCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as HX
import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT

------------------------------------------------------------------------
-- CANONICAL H_X -> H_T COMPILER
--
-- The historical H_T owner looked like an additional Fourier/Weyl theorem.
-- On the canonical H_X carrier, however, its actual intertwining equation is
-- already the character product theorem:
--
--   exp(i (b-t) u) = exp(-i t u) exp(i b u).
--
-- H_X owns both the source/gap exponential identifications and the exact
-- target-times-source = gap-character theorem.  Therefore the H_T intertwiner
-- is compiler output from the SAME H_X object.  No new Monster/F3 theorem and
-- no second analytic character action are required.
------------------------------------------------------------------------

≡-sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

sourceAtGapIsGapCharacter :
  ∀ {analytic} →
  (H_X : HX.RiemannComplexCharacterExtension analytic) →
  (b t u : HX.RealCarrier H_X) →
  HX.sourceCharacter H_X (HX.subR H_X b t) u
  ≡ HX.gapCharacter H_X b t u
sourceAtGapIsGapCharacter H_X b t u =
  ≡-trans
    (HX.sourceCharacterIsExpIBU H_X (HX.subR H_X b t) u)
    (≡-sym (HX.gapCharacterIsExpIGapU H_X b t u))

canonicalHXIntertwines :
  ∀ {analytic} →
  (H_X : HX.RiemannComplexCharacterExtension analytic) →
  (u : HX.RealCarrier H_X) →
  (t b : HX.RealCarrier H_X) →
  HX.sourceCharacter H_X (HX.subR H_X b t) u
  ≡ HX.mulC H_X
      (HX.targetCharacter H_X t u)
      (HX.sourceCharacter H_X b u)
canonicalHXIntertwines H_X u t b =
  ≡-trans
    (sourceAtGapIsGapCharacter H_X b t u)
    (≡-sym (HX.targetTimesSourceIsGapCharacter H_X b t u))

canonicalHXToHT :
  ∀ {analytic} →
  HX.RiemannComplexCharacterExtension analytic →
  HT.TargetTranslationModulationIntertwiner
canonicalHXToHT H_X =
  HT.target-translation-modulation-intertwiner
    (HX.RealCarrier H_X)
    (HX.RealCarrier H_X)
    (HX.ComplexCarrier H_X)
    (λ t b → HX.subR H_X b t)
    (λ u b → HX.sourceCharacter H_X b u)
    (HX.mulC H_X)
    (λ u t → HX.targetCharacter H_X t u)
    (canonicalHXIntertwines H_X)
    ((t b : HX.RealCarrier H_X) →
      (λ t' b' → HX.subR H_X b' t') t b
      ≡ HX.subR H_X b t)
    ((delta u : HX.RealCarrier H_X) →
      HX.realPart H_X
        (HX.expC H_X (HX.plusIProduct H_X delta u))
      ≡ HX.cosR H_X (HX.mulR H_X delta u))
    ⊤
    ⊤
    (HX.characterReference H_X)

------------------------------------------------------------------------
-- Search consequences.
------------------------------------------------------------------------

data HTSearchAction : Set where
  rebuildTranslationModulationIntertwiner
  compileHTFromCanonicalHX
  attachHTToPoleNearAdapter
  : HTSearchAction

data SearchStatus : Set where
  pruned downstream : SearchStatus

searchStatus : HTSearchAction → SearchStatus
searchStatus rebuildTranslationModulationIntertwiner = pruned
searchStatus compileHTFromCanonicalHX = downstream
searchStatus attachHTToPoleNearAdapter = downstream

htRebuildPruned :
  searchStatus rebuildTranslationModulationIntertwiner ≡ pruned
htRebuildPruned = refl

record CanonicalHXToHTBoundary : Set where
  constructor canonical-hx-to-ht-boundary
  field
    hTNeedsIndependentFourierWeylTheoremAfterHX : Bool
    hTNeedsIndependentFourierWeylTheoremAfterHXIsFalse :
      hTNeedsIndependentFourierWeylTheoremAfterHX ≡ false

    hXCharacterProductAlreadyImpliesHTIntertwining : Bool
    hXCharacterProductAlreadyImpliesHTIntertwiningIsTrue :
      hXCharacterProductAlreadyImpliesHTIntertwining ≡ true

    reflectionEvenCosineAlreadyOwnedByHX : Bool
    reflectionEvenCosineAlreadyOwnedByHXIsTrue :
      reflectionEvenCosineAlreadyOwnedByHX ≡ true

    monsterRepresentationUsedAsProofAuthority : Bool
    monsterRepresentationUsedAsProofAuthorityIsFalse :
      monsterRepresentationUsedAsProofAuthority ≡ false

    hTCompilerClosedConditionallyOnHX : Bool
    hTCompilerClosedConditionallyOnHXIsTrue :
      hTCompilerClosedConditionallyOnHX ≡ true

    hXRecoveredHere : Bool
    hXRecoveredHereIsFalse : hXRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHXToHTBoundary : CanonicalHXToHTBoundary
canonicalHXToHTBoundary =
  canonical-hx-to-ht-boundary
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "The historical H_T intertwiner is not a new analytic theorem once canonical H_X is owned. On that exact carrier, translateToTarget is b-t, modulation is the source character exp(+ibu), and the H_T law follows by identifying the source character at b-t with the gap character and then reversing H_X's target-times-source = gap theorem. H_X also already owns the reflection-even cosine projection. Therefore rebuild-H_T is pruned; recover/attach canonical H_X, then compile H_T. No Monster representation is proof authority and RH is not derived."
