module DASHI.Analysis.RiemannG2CanonicalHXHMToPoleNearHTAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as HX
import DASHI.Analysis.RiemannAnalyticModulationExtensionExact as HM
import DASHI.Analysis.RiemannPoleNearHTAnalyticAdapterExact as Adapter
import DASHI.Analysis.RiemannG2CanonicalHXToHTCompilerExact as HXHT

------------------------------------------------------------------------
-- CANONICAL H_X + H_M -> POLE-NEAR H_T ADAPTER
--
-- The adapter record historically looked like another scientific leaf, but its
-- only theorem-bearing H_T field is now compiler output from canonical H_X.
-- The remaining adapter coordinates are same-object/provenance sockets tying
-- that H_T to the selected H_M, Weil carrier and concrete explicit formula.
-- Hence, once the literal H_M exists on those indexed objects, the adapter is a
-- compiler/attachment payment rather than new Fourier analysis.
------------------------------------------------------------------------

canonicalHXHMToPoleNearHTAdapter :
  ∀ {analytic space formula compat} →
  (H_X : HX.RiemannComplexCharacterExtension analytic) →
  (H_M : HM.RiemannAnalyticModulationExtension analytic space formula compat) →
  Adapter.PoleNearHTAnalyticAdapter analytic space formula compat H_M
canonicalHXHMToPoleNearHTAdapter {analytic} {space} {formula} {compat} H_X H_M =
  Adapter.pole-near-ht-analytic-adapter
    (HXHT.canonicalHXToHT H_X)
    -- same canonical analytic carrier
    ⊤
    -- same canonical Weil test carrier
    ⊤
    -- same concrete explicit formula
    ⊤
    -- literal b-t target translation
    ((t b : HX.RealCarrier H_X) →
      (λ t' b' → HX.subR H_X b' t') t b
      ≡ HX.subR H_X b t)
    -- target character = exp(-itu)
    ((t u : HX.RealCarrier H_X) →
      HX.targetCharacter H_X t u
      ≡ HX.expC H_X (HX.minusIProduct H_X t u))
    -- unshifted source character = exp(+ibu)
    ((b u : HX.RealCarrier H_X) →
      HX.sourceCharacter H_X b u
      ≡ HX.expC H_X (HX.plusIProduct H_X b u))
    -- product is the literal shifted gap character
    ((b t u : HX.RealCarrier H_X) →
      HX.mulC H_X
        (HX.targetCharacter H_X t u)
        (HX.sourceCharacter H_X b u)
      ≡ HX.gapCharacter H_X b t u)
    -- reflection-even response is the canonical cosine theorem
    ((delta u : HX.RealCarrier H_X) →
      HX.realPart H_X
        (HX.expC H_X (HX.plusIProduct H_X delta u))
      ≡ HX.cosR H_X (HX.mulR H_X delta u))
    -- pole normalization remains a same-object attachment socket downstream.
    ⊤
    (HX.characterReference H_X)

------------------------------------------------------------------------
-- Search consequence.
------------------------------------------------------------------------

data PoleNearHTSearchAction : Set where
  rebuildHTIntertwiner
  buildFreshPoleNearAdapter
  recoverCanonicalHMFactorization
  compilePoleNearAdapter
  proceedToWindowRestriction
  : PoleNearHTSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : PoleNearHTSearchAction → SearchStatus
searchStatus rebuildHTIntertwiner = pruned
searchStatus buildFreshPoleNearAdapter = pruned
searchStatus recoverCanonicalHMFactorization = live
searchStatus compilePoleNearAdapter = downstream
searchStatus proceedToWindowRestriction = downstream

freshAdapterSearchPruned :
  searchStatus buildFreshPoleNearAdapter ≡ pruned
freshAdapterSearchPruned = refl

record CanonicalHXHMToPoleNearHTBoundary : Set where
  constructor canonical-hx-hm-to-pole-near-ht-boundary
  field
    hTIntertwinerNeedsReproofAfterCanonicalHX : Bool
    hTIntertwinerNeedsReproofAfterCanonicalHXIsFalse :
      hTIntertwinerNeedsReproofAfterCanonicalHX ≡ false

    poleNearAdapterNeedsIndependentAnalyticConstructionAfterHXHM : Bool
    poleNearAdapterNeedsIndependentAnalyticConstructionAfterHXHMIsFalse :
      poleNearAdapterNeedsIndependentAnalyticConstructionAfterHXHM ≡ false

    sameObjectAttachmentStillRequired : Bool
    sameObjectAttachmentStillRequiredIsTrue : sameObjectAttachmentStillRequired ≡ true

    nextLiveMathematicalLeafIsHMFactorization : Bool
    nextLiveMathematicalLeafIsHMFactorizationIsTrue :
      nextLiveMathematicalLeafIsHMFactorization ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHXHMToPoleNearHTBoundary : CanonicalHXHMToPoleNearHTBoundary
canonicalHXHMToPoleNearHTBoundary =
  canonical-hx-hm-to-pole-near-ht-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    "Canonical H_X already compiles the exact translation/modulation intertwiner and cosine projection. Therefore, once canonical H_M exists on the indexed analytic/Weil/formula objects, the pole-near H_T adapter is only a same-object attachment compiler; do not search for another H_T theorem or fresh adapter. The live mathematical seam upstream is the one pointwise H_M phase-action factorisation. After that, advance to the window/restriction layer. RH is not derived."
