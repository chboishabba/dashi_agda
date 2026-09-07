module DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact where

------------------------------------------------------------------------
-- J / COLOUR-WHEEL / WAVE / SIGNED-FRACTRAN BIDI CROSS-POLLINATION
--
-- INTROSPECTIVE STATUS
--
-- The observed three-way colour fans and complementary circular patterns are
-- treated as prompts to inspect an already-owned finite phase/spectral seam.
-- They are not treated as source evidence for theta functions, j, or Monster.
--
-- Exact repository mathematics reused here:
--   * HexTruth -> triadic phase + binary orientation (Base369MobiusTransport),
--   * C3 spectral sectors 0,+,- and conjugation (27 spectral owner),
--   * fold/unfold of signed ternary kernel states (TriadicKernelLift...),
--   * signed FRACTRAN multiplicity -> negative/zero/positive coarse trit,
--   * wave coefficient cells retaining exact payload + ternary orientation,
--   * BIDI exact-plus-residual search discipline.
--
-- External/source layer:
--   * JInvariantSourceAtlasExact owns the revision-pinned secondary j/theta/
--     lambda/moonshine statements.  This file derives no analytic theorem from
--     those strings.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; tri-low ; tri-mid ; tri-high
  )

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Wave
import DASHI.Foundations.Base369PolyphaseCharacters as Polyphase
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariantLambdaOrbitBase369BridgeExact as Lambda
import DASHI.Moonshine.JInvariantSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. Exact six-state colour-wheel chart.
--
-- "Curl" is only a finite chart name: HexTruth is the cyclic six-state wheel;
-- "uncurl" exposes the already-owned product coordinates
--     triadic phase x binary orientation.
-- No Euclidean embedding or analytic colour model is asserted.
------------------------------------------------------------------------

record UncurledSix : Set where
  constructor uncurledSix
  field
    phase : TriTruth
    polarity : Mobius.OrientationPolarity

open UncurledSix public

uncurlSix : HexTruth → UncurledSix
uncurlSix h =
  uncurledSix
    (Mobius.hexTriadicPhase h)
    (Mobius.hexOrientationPolarity h)

curlSix : UncurledSix → HexTruth
curlSix (uncurledSix tri-low  Mobius.positive) = hex-0
curlSix (uncurledSix tri-mid  Mobius.positive) = hex-1
curlSix (uncurledSix tri-high Mobius.positive) = hex-2
curlSix (uncurledSix tri-low  Mobius.negative) = hex-3
curlSix (uncurledSix tri-mid  Mobius.negative) = hex-4
curlSix (uncurledSix tri-high Mobius.negative) = hex-5

curlAfterUncurl : (h : HexTruth) → curlSix (uncurlSix h) ≡ h
curlAfterUncurl hex-0 = refl
curlAfterUncurl hex-1 = refl
curlAfterUncurl hex-2 = refl
curlAfterUncurl hex-3 = refl
curlAfterUncurl hex-4 = refl
curlAfterUncurl hex-5 = refl

uncurlAfterCurl : (u : UncurledSix) → uncurlSix (curlSix u) ≡ u
uncurlAfterCurl (uncurledSix tri-low  Mobius.positive) = refl
uncurlAfterCurl (uncurledSix tri-mid  Mobius.positive) = refl
uncurlAfterCurl (uncurledSix tri-high Mobius.positive) = refl
uncurlAfterCurl (uncurledSix tri-low  Mobius.negative) = refl
uncurlAfterCurl (uncurledSix tri-mid  Mobius.negative) = refl
uncurlAfterCurl (uncurledSix tri-high Mobius.negative) = refl

flipUncurledOrientation : UncurledSix → UncurledSix
flipUncurledOrientation (uncurledSix p o) =
  uncurledSix p (Mobius.flipOrientationPolarity o)

mobiusTransportIsOrientationFlipAfterUncurl :
  (h : HexTruth) →
  uncurlSix (Mobius.mobiusTransport h) ≡
  flipUncurledOrientation (uncurlSix h)
mobiusTransportIsOrientationFlipAfterUncurl hex-0 = refl
mobiusTransportIsOrientationFlipAfterUncurl hex-1 = refl
mobiusTransportIsOrientationFlipAfterUncurl hex-2 = refl
mobiusTransportIsOrientationFlipAfterUncurl hex-3 = refl
mobiusTransportIsOrientationFlipAfterUncurl hex-4 = refl
mobiusTransportIsOrientationFlipAfterUncurl hex-5 = refl

------------------------------------------------------------------------
-- 2. The same uncurled chart is carried by the finite lambda-label bridge.
------------------------------------------------------------------------

uncurlLambda : Lambda.LambdaOrbitTag → UncurledSix
uncurlLambda l =
  uncurledSix
    (Lambda.lambdaPairPhase l)
    (Lambda.lambdaOrientation l)

lambdaUncurlAgreesWithHexUncurl :
  (h : HexTruth) →
  uncurlLambda (Lambda.hexToLambdaOrbit h) ≡ uncurlSix h
lambdaUncurlAgreesWithHexUncurl hex-0 = refl
lambdaUncurlAgreesWithHexUncurl hex-1 = refl
lambdaUncurlAgreesWithHexUncurl hex-2 = refl
lambdaUncurlAgreesWithHexUncurl hex-3 = refl
lambdaUncurlAgreesWithHexUncurl hex-4 = refl
lambdaUncurlAgreesWithHexUncurl hex-5 = refl

lambdaComplementIsOrientationFlipAfterUncurl :
  (l : Lambda.LambdaOrbitTag) →
  uncurlLambda (Lambda.lambdaComplement l) ≡
  flipUncurledOrientation (uncurlLambda l)
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaIdentity = refl
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaOneOverOneMinus = refl
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaMinusOneOverLambda = refl
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaReciprocal = refl
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaOverLambdaMinusOne = refl
lambdaComplementIsOrientationFlipAfterUncurl Lambda.lambdaOneMinus = refl

------------------------------------------------------------------------
-- 3. Exact three-state spectral unrolling.
--
-- The three spectral labels are equivalent, as a finite carrier only, to the
-- signed ternary kernel and SSP trit.  This does not identify their payloads.
------------------------------------------------------------------------

kernelToFrequency : Triadic.KernelTrit → Spectral.AxisFrequency
kernelToFrequency Triadic.negativeTrit = Spectral.frequencyNegative
kernelToFrequency Triadic.zeroTrit = Spectral.frequencyZero
kernelToFrequency Triadic.positiveTrit = Spectral.frequencyPositive

frequencyToKernel : Spectral.AxisFrequency → Triadic.KernelTrit
frequencyToKernel Spectral.frequencyNegative = Triadic.negativeTrit
frequencyToKernel Spectral.frequencyZero = Triadic.zeroTrit
frequencyToKernel Spectral.frequencyPositive = Triadic.positiveTrit

frequencyKernelRoundTrip :
  (f : Spectral.AxisFrequency) →
  kernelToFrequency (frequencyToKernel f) ≡ f
frequencyKernelRoundTrip Spectral.frequencyNegative = refl
frequencyKernelRoundTrip Spectral.frequencyZero = refl
frequencyKernelRoundTrip Spectral.frequencyPositive = refl

kernelFrequencyRoundTrip :
  (t : Triadic.KernelTrit) →
  frequencyToKernel (kernelToFrequency t) ≡ t
kernelFrequencyRoundTrip Triadic.negativeTrit = refl
kernelFrequencyRoundTrip Triadic.zeroTrit = refl
kernelFrequencyRoundTrip Triadic.positiveTrit = refl

sspToFrequency : SSP.SSPTrit → Spectral.AxisFrequency
sspToFrequency SSP.sspNegOne = Spectral.frequencyNegative
sspToFrequency SSP.sspZero = Spectral.frequencyZero
sspToFrequency SSP.sspPosOne = Spectral.frequencyPositive

frequencyToSSP : Spectral.AxisFrequency → SSP.SSPTrit
frequencyToSSP Spectral.frequencyNegative = SSP.sspNegOne
frequencyToSSP Spectral.frequencyZero = SSP.sspZero
frequencyToSSP Spectral.frequencyPositive = SSP.sspPosOne

sspFrequencyRoundTrip :
  (t : SSP.SSPTrit) → frequencyToSSP (sspToFrequency t) ≡ t
sspFrequencyRoundTrip SSP.sspNegOne = refl
sspFrequencyRoundTrip SSP.sspZero = refl
sspFrequencyRoundTrip SSP.sspPosOne = refl

frequencySSPRoundTrip :
  (f : Spectral.AxisFrequency) → sspToFrequency (frequencyToSSP f) ≡ f
frequencySSPRoundTrip Spectral.frequencyNegative = refl
frequencySSPRoundTrip Spectral.frequencyZero = refl
frequencySSPRoundTrip Spectral.frequencyPositive = refl

------------------------------------------------------------------------
-- 4. Signed FRACTRAN negation is spectral conjugation at the coarse observer.
--
-- Magnitude remains in SignedMultiplicity; only its coarse signed orientation
-- is sent to the C3 spectral label.  Therefore this theorem is genuinely
-- observer-level and does not collapse FRACTRAN arithmetic into Fourier data.
------------------------------------------------------------------------

signedMultiplicityFrequency :
  Signed.SignedMultiplicity → Spectral.AxisFrequency
signedMultiplicityFrequency m =
  kernelToFrequency (Signed.coarseMultiplicity m)

signedNegationBecomesSpectralConjugation :
  (m : Signed.SignedMultiplicity) →
  signedMultiplicityFrequency (Signed.negateMultiplicity m) ≡
  Spectral.conjugateFrequency (signedMultiplicityFrequency m)
signedNegationBecomesSpectralConjugation (Signed.negativeMultiplicity n) = refl
signedNegationBecomesSpectralConjugation Signed.zeroMultiplicity = refl
signedNegationBecomesSpectralConjugation (Signed.positiveMultiplicity n) = refl

frequencyToFRACTRANOrientation :
  Spectral.AxisFrequency → Signed.FibreOrientation
frequencyToFRACTRANOrientation Spectral.frequencyNegative = Signed.inverseOrientation
frequencyToFRACTRANOrientation Spectral.frequencyZero = Signed.mediatedOrientation
frequencyToFRACTRANOrientation Spectral.frequencyPositive = Signed.forwardOrientation

spectralObserverRecoversFRACTRANOrientation :
  (m : Signed.SignedMultiplicity) →
  frequencyToFRACTRANOrientation (signedMultiplicityFrequency m) ≡
  Signed.orientationOfMultiplicity m
spectralObserverRecoversFRACTRANOrientation (Signed.negativeMultiplicity n) = refl
spectralObserverRecoversFRACTRANOrientation Signed.zeroMultiplicity = refl
spectralObserverRecoversFRACTRANOrientation (Signed.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- 5. Wave/multiresolution cells already supply the exact "colour payload in
--    the fibre, three-sector address outside" architecture.
------------------------------------------------------------------------

cellFrequency :
  {Scale Position Coefficient : Set} →
  {quantizeCoefficient : Coefficient → SSP.SSPTrit} →
  Wave.CoefficientCell Scale Position Coefficient quantizeCoefficient →
  Spectral.AxisFrequency
cellFrequency cell =
  sspToFrequency
    (Wave.orientation (Wave.coefficientAddress cell))

cellExactPayloadSurvivesUnrolling :
  {Scale Position Coefficient : Set} →
  {quantizeCoefficient : Coefficient → SSP.SSPTrit} →
  (cell : Wave.CoefficientCell Scale Position Coefficient quantizeCoefficient) →
  Wave.exactCoefficient cell ≡ Wave.exactCoefficient cell
cellExactPayloadSurvivesUnrolling = Wave.coefficientValueSurvivesAddressing

------------------------------------------------------------------------
-- 6. BIDI proof-search cut.
--
-- Forward search has now reached a reversible finite wheel chart, wave-address
-- spectral observer, and signed-FRACTRAN/conjugation intertwiner.
-- Backward search from the theta/j consumer still demands an analytic complex
-- phase carrier.  The existing Polyphase owner explicitly leaves complex root
-- realization and Fourier reconstruction unpromoted, so that is the first
-- residual -- before theta identity, j same-object welding, or Monster action.
------------------------------------------------------------------------

data ColourWheelAnalyticResidual : Set where
  missingComplexRootOfUnityRealisation : ColourWheelAnalyticResidual
  missingFourierReconstruction : ColourWheelAnalyticResidual
  missingThetaSameObjectRealisation : ColourWheelAnalyticResidual
  missingJSameObjectWeld : ColourWheelAnalyticResidual
  missingMonsterActionIntertwiner : ColourWheelAnalyticResidual

firstColourWheelAnalyticResidual : ColourWheelAnalyticResidual
firstColourWheelAnalyticResidual = missingComplexRootOfUnityRealisation

record FiniteColourWheelExact : Set₁ where
  constructor finite-colour-wheel-exact
  field
    sixUncurlRoundTrip : (h : HexTruth) → curlSix (uncurlSix h) ≡ h
    mobiusUncurlIntertwiner :
      (h : HexTruth) →
      uncurlSix (Mobius.mobiusTransport h) ≡
      flipUncurledOrientation (uncurlSix h)
    signedNegationConjugation :
      (m : Signed.SignedMultiplicity) →
      signedMultiplicityFrequency (Signed.negateMultiplicity m) ≡
      Spectral.conjugateFrequency (signedMultiplicityFrequency m)
    lambdaUncurlIntertwiner :
      (l : Lambda.LambdaOrbitTag) →
      uncurlLambda (Lambda.lambdaComplement l) ≡
      flipUncurledOrientation (uncurlLambda l)

finiteColourWheelExact : FiniteColourWheelExact
finiteColourWheelExact =
  finite-colour-wheel-exact
    curlAfterUncurl
    mobiusTransportIsOrientationFlipAfterUncurl
    signedNegationBecomesSpectralConjugation
    lambdaComplementIsOrientationFlipAfterUncurl

colourWheelBidiCut :
  Bidi.ApproximationWithResidualObligation
    FiniteColourWheelExact
    ColourWheelAnalyticResidual
colourWheelBidiCut =
  Bidi.approximationWithResidualObligation
    finiteColourWheelExact
    firstColourWheelAnalyticResidual

------------------------------------------------------------------------
-- 7. Introspective/source firewall.
------------------------------------------------------------------------

record ColourWheelIntrospectiveBoundary : Set where
  constructor colour-wheel-introspective-boundary
  field
    finiteCurlUncurlExact : Bool
    signedFRACTRANNegationMatchesSpectralConjugation : Bool
    waveCellRetainsExactContinuousPayload : Bool
    lambdaFinitePairingUsesSameUncurledChart : Bool
    complexRootOfUnityRealisationAlreadyPromoted : Bool
    FourierReconstructionAlreadyPromoted : Bool
    visualRainbowIsThetaIdentity : Bool
    finiteWheelIsAnalyticLambdaAction : Bool
    finiteSpectralObserverIsMonsterRepresentation : Bool
    signedFRACTRANArithmeticEqualsWaveAmplitude : Bool

canonicalColourWheelIntrospectiveBoundary : ColourWheelIntrospectiveBoundary
canonicalColourWheelIntrospectiveBoundary =
  colour-wheel-introspective-boundary
    true true true true false false false false false false

polyphaseStillBlocksComplexPromotion :
  Polyphase.PolyphaseCharacterAnalyticBoundary.complexRootOfUnityRealisationPromoted
    Polyphase.polyphaseCharacterAnalyticBoundary ≡ false
polyphaseStillBlocksComplexPromotion = refl

polyphaseStillBlocksFourierReconstruction :
  Polyphase.PolyphaseCharacterAnalyticBoundary.FourierReconstructionPromoted
    Polyphase.polyphaseCharacterAnalyticBoundary ≡ false
polyphaseStillBlocksFourierReconstruction = refl

visualPromptStillNotSourceClaim :
  Sources.JSourceAttributionBoundary.visualPatternIsSourceEntitledClaim
    Sources.canonicalJSourceAttributionBoundary ≡ false
visualPromptStillNotSourceClaim = refl
