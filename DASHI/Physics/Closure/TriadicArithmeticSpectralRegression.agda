module DASHI.Physics.Closure.TriadicArithmeticSpectralRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; Stream; TritPrefix; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Physics.Closure.TriadicSectorQSeries as QS
import DASHI.Physics.Closure.TriadicRepresentationMDL as MDL
import DASHI.Physics.Closure.TriadicArithmeticSpectralAssembly as Assembly

open QS.QSeriesCarrier using (Coeff; zeroᶜ; oneᶜ; _+ᶜ_; _*ᶜ_)
open QS.SectorTraceTower using (Sector; traceCoefficient)
open QS using (Vec) renaming ([] to []q; _∷_ to _∷q_)

infixr 5 _∷q_

------------------------------------------------------------------------
-- Canonical [-1, 0, +1] stream.

canonicalStream : Stream
canonicalStream zero = neg
canonicalStream (suc zero) = zer
canonicalStream (suc (suc zero)) = pos
canonicalStream (suc (suc (suc n))) = zer

canonicalDepthThree : Q.Residue3Pow Q.three
canonicalDepthThree = neg ∷ zer ∷ pos ∷ []

canonicalDepthTwo : Q.Residue3Pow Q.two
canonicalDepthTwo = neg ∷ zer ∷ []

projectionDepthThreeExact :
  Q.projection Q.three canonicalStream ≡ canonicalDepthThree
projectionDepthThreeExact = refl

reductionDepthThreeExact :
  Q.reduce canonicalDepthThree ≡ canonicalDepthTwo
reductionDepthThreeExact = refl

streamInverseLimitCompatibilityAtTwo :
  Q.reduce
    (Q.coordinate (Q.streamToInverseLimit canonicalStream) Q.three)
  ≡ Q.coordinate (Q.streamToInverseLimit canonicalStream) Q.two
streamInverseLimitCompatibilityAtTwo =
  Q.compatible (Q.streamToInverseLimit canonicalStream) Q.two

------------------------------------------------------------------------
-- Carry arithmetic examples.

oneDigitPositive : Q.Residue3Pow Q.one
oneDigitPositive = pos ∷ []

oneDigitNegative : Q.Residue3Pow Q.one
oneDigitNegative = neg ∷ []

positivePlusPositiveModThree :
  Arithmetic.addResidue oneDigitPositive oneDigitPositive
  ≡ oneDigitNegative
positivePlusPositiveModThree = refl

fourResidue : Q.Residue3Pow Q.two
fourResidue = pos ∷ pos ∷ []

minusOneResidueModNine : Q.Residue3Pow Q.two
minusOneResidueModNine = neg ∷ zer ∷ []

fourPlusFourModNine :
  Arithmetic.addResidue fourResidue fourResidue
  ≡ minusOneResidueModNine
fourPlusFourModNine = refl

canonicalAdditiveInverse :
  Arithmetic.addResidue
    (Arithmetic.negateResidue canonicalDepthThree)
    canonicalDepthThree
  ≡ Arithmetic.zeroResidue Q.three
canonicalAdditiveInverse =
  Arithmetic.leftInverse canonicalDepthThree

------------------------------------------------------------------------
-- Exact spectral-codec baseline.

natIdentityCodec : Irrep.ExactSpectralCodec Q.two
natIdentityCodec = Irrep.identitySpectralCodec Q.two Nat

identityCodecRoundTrip :
  (f : Irrep.Signal Q.two Nat) →
  (x : Q.Residue3Pow Q.two) →
  Irrep.synthesize natIdentityCodec
    (Irrep.analyze natIdentityCodec f)
    x
  ≡ f x
identityCodecRoundTrip = Irrep.reconstructAnalyze natIdentityCodec

------------------------------------------------------------------------
-- Exact finite q-series prefix.

data Unit : Set where
  unit : Unit

natQSeriesCarrier : QS.QSeriesCarrier
natQSeriesCarrier =
  record
    { Coeff = Nat
    ; zeroᶜ = zero
    ; oneᶜ = Q.one
    ; _+ᶜ_ = Q._+ⁿ_
    ; _*ᶜ_ = Q._*ⁿ_
    }

natTraceTower : QS.SectorTraceTower natQSeriesCarrier
natTraceTower =
  record
    { Sector = Unit
    ; traceCoefficient = λ n sector → n
    }

expectedNatPrefixThree : Vec Nat Q.three
expectedNatPrefixThree =
  zero ∷q Q.one ∷q Q.two ∷q []q

qSeriesPrefixThreeExact :
  QS.qSeriesPrefix
    natQSeriesCarrier
    natTraceTower
    unit
    Q.three
  ≡ expectedNatPrefixThree
qSeriesPrefixThreeExact = refl

------------------------------------------------------------------------
-- Bounded MDL depth and promotion-status regressions.

depthTwoBelowThree : MDL.DepthBelow Q.three
depthTwoBelowThree =
  MDL.depthNext (MDL.depthNext MDL.depthZero)

depthTwoValueExact :
  MDL.depthValue depthTwoBelowThree ≡ Q.two
depthTwoValueExact = refl

realSmoothPromotionRemainsFalse :
  Assembly.realSmoothZ3Promoted Assembly.currentLayerStatus
  ≡ false
realSmoothPromotionRemainsFalse =
  Assembly.realSmoothZ3StillNotPromoted
