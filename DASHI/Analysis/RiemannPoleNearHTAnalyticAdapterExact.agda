module DASHI.Analysis.RiemannPoleNearHTAnalyticAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticModulationExtensionExact as Mod
import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT

record PoleNearHTAnalyticAdapter
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space)
    (modulation : Mod.RiemannAnalyticModulationExtension analytic space compat) : Set₁ where
  constructor pole-near-ht-analytic-adapter
  field
    H_T : HT.TargetTranslationModulationIntertwiner

    usesCanonicalAnalyticCarrier : Set
    usesCanonicalWeilTestCarrier : Set
    targetTranslationIsLiteralGap : Set
    targetCharacterIsExpMinusTargetFrequency : Set
    unshiftedCharacterIsExpZeroFrequency : Set
    productCharacterIsShiftedGapCharacter : Set
    reflectionEvenPartIsLiteralPoleCosine : Set
    samePoleNormalization : Set

    adapterReference : String

open PoleNearHTAnalyticAdapter public

record PoleNearHTAnalyticAdapterBoundary : Set where
  constructor pole-near-ht-analytic-adapter-boundary
  field
    canonicalAnalyticCarrierAlreadyProvidesAdapter : Bool
    canonicalAnalyticCarrierAlreadyProvidesAdapterIsFalse :
      canonicalAnalyticCarrierAlreadyProvidesAdapter ≡ false

    modulationExtensionNeededFirst : Bool
    modulationExtensionNeededFirstIsTrue : modulationExtensionNeededFirst ≡ true

    literalGapAndCharacterLawsRequired : Bool
    literalGapAndCharacterLawsRequiredIsTrue : literalGapAndCharacterLawsRequired ≡ true

    reflectionEvenCosineLawRequired : Bool
    reflectionEvenCosineLawRequiredIsTrue : reflectionEvenCosineLawRequired ≡ true

    monsterFiniteCharacterCanCloseAdapter : Bool
    monsterFiniteCharacterCanCloseAdapterIsFalse : monsterFiniteCharacterCanCloseAdapter ≡ false

    H_TClosed : Bool
    H_TClosedIsFalse : H_TClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

canonicalPoleNearHTAnalyticAdapterBoundary : PoleNearHTAnalyticAdapterBoundary
canonicalPoleNearHTAnalyticAdapterBoundary =
  pole-near-ht-analytic-adapter-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "On the canonical Riemann analytic and Weil carriers, add the missing target modulation operation and prove its character law, then identify the reflection-even response with the exact pole-quotient cosine normalization."
