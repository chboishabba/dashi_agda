module DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic

------------------------------------------------------------------------
-- H_X: COMPLEX CHARACTER ALGEBRA ON THE CANONICAL RIEMANN CARRIER
--
-- The canonical ComplexAnalyticCarrier deliberately stops before real-field
-- arithmetic, real embedding, i, complex exponential and trigonometric
-- projection.  H_X adds exactly the operations needed to state the target
-- character law on that SAME carrier.
--
-- Intended identities:
--   chi_t(u)   = exp(- i t u)
--   chi_b(u)   = exp(+ i b u)
--   chi_gap    = exp(+ i (b-t) u)
--   chi_t chi_b = chi_gap.
--
-- The pole factor 4 g(u) cosh(a u) is NOT part of H_X.  It belongs to the
-- separately source-pinned reflection-pair kernel normalization.
------------------------------------------------------------------------

record RiemannComplexCharacterExtension
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  constructor riemann-complex-character-extension
  field
    carrierAgreementUsed : Set

    -- These are the actual Real/Complex carriers of AnalyticSubstrate.carrier.
    RealCarrier ComplexCarrier : Set
    realCarrierIsCanonical : Set
    complexCarrierIsCanonical : Set

    zeroR : RealCarrier
    addR mulR : RealCarrier → RealCarrier → RealCarrier
    negR : RealCarrier → RealCarrier
    subR : RealCarrier → RealCarrier → RealCarrier
    subRIsAddNeg : (b t : RealCarrier) → subR b t ≡ addR b (negR t)

    embedReal : RealCarrier → ComplexCarrier
    imaginaryUnit : ComplexCarrier
    addC mulC : ComplexCarrier → ComplexCarrier → ComplexCarrier
    negC : ComplexCarrier → ComplexCarrier
    realPart : ComplexCarrier → RealCarrier

    expC : ComplexCarrier → ComplexCarrier
    cosR : RealCarrier → RealCarrier

    -- Canonical phase arguments.
    plusIProduct : RealCarrier → RealCarrier → ComplexCarrier
    minusIProduct : RealCarrier → RealCarrier → ComplexCarrier

    plusIProductIsCanonical : Set
    minusIProductIsCanonical : Set

    targetCharacter : RealCarrier → RealCarrier → ComplexCarrier
    sourceCharacter : RealCarrier → RealCarrier → ComplexCarrier
    gapCharacter : RealCarrier → RealCarrier → RealCarrier → ComplexCarrier

    targetCharacterIsExpMinusITU :
      (t u : RealCarrier) →
      targetCharacter t u ≡ expC (minusIProduct t u)

    sourceCharacterIsExpIBU :
      (b u : RealCarrier) →
      sourceCharacter b u ≡ expC (plusIProduct b u)

    gapCharacterIsExpIGapU :
      (b t u : RealCarrier) →
      gapCharacter b t u ≡ expC (plusIProduct (subR b t) u)

    exponentialAdditiveLaw :
      (x y : ComplexCarrier) →
      expC (addC x y) ≡ mulC (expC x) (expC y)

    targetPlusSourceExponentIsGapExponent :
      (b t u : RealCarrier) →
      addC (minusIProduct t u) (plusIProduct b u)
      ≡ plusIProduct (subR b t) u

    targetTimesSourceIsGapCharacter :
      (b t u : RealCarrier) →
      mulC (targetCharacter t u) (sourceCharacter b u)
      ≡ gapCharacter b t u

    -- Backward consumer hook: only the even real character is cosine.
    reflectionEvenCharacterIsCosine :
      (delta u : RealCarrier) →
      realPart (expC (plusIProduct delta u)) ≡ cosR (mulR delta u)

    characterReference : String

open RiemannComplexCharacterExtension public

record ComplexCharacterExtensionBoundary : Set where
  constructor complex-character-extension-boundary
  field
    canonicalCarrierAlreadyOwnsRealFieldArithmetic : Bool
    canonicalCarrierAlreadyOwnsRealFieldArithmeticIsFalse :
      canonicalCarrierAlreadyOwnsRealFieldArithmetic ≡ false

    canonicalCarrierAlreadyOwnsComplexExponential : Bool
    canonicalCarrierAlreadyOwnsComplexExponentialIsFalse :
      canonicalCarrierAlreadyOwnsComplexExponential ≡ false

    characterMustLiveOnCanonicalCarrier : Bool
    characterMustLiveOnCanonicalCarrierIsTrue :
      characterMustLiveOnCanonicalCarrier ≡ true

    evenProjectionMustRecoverCosine : Bool
    evenProjectionMustRecoverCosineIsTrue :
      evenProjectionMustRecoverCosine ≡ true

    poleCoshAndTaperFactorBelongsToCharacterLaw : Bool
    poleCoshAndTaperFactorBelongsToCharacterLawIsFalse :
      poleCoshAndTaperFactorBelongsToCharacterLaw ≡ false

    H_XClosed : Bool
    H_XClosedIsFalse : H_XClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

canonicalComplexCharacterExtensionBoundary : ComplexCharacterExtensionBoundary
canonicalComplexCharacterExtensionBoundary =
  complex-character-extension-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Construct the real arithmetic/embedding, imaginary unit, complex exponential and cosine projection on the canonical Riemann analytic carrier, then prove exp(-itu) exp(ibu) = exp(i(b-t)u) and the even real projection cos((b-t)u)."
