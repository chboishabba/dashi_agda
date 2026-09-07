module DASHI.Physics.Closure.NSTriadKNCauchyInitialAmplitudeEndpointRound461Exact where

------------------------------------------------------------------------
-- ROUND461 / PHYSICAL CAUCHY INITIAL ENDPOINT -> AMPLITUDE-SQUARE BUDGET
--
-- R460 isolates the finite combinatorics.  This file instantiates its abstract
-- pair flux with the literal R447/R446 Cauchy-Hermitian pair
--
--   2 K(rho_i,rho_j) Re<D_i,D_j>.
--
-- A shared positive rate floor m gives
--
--   K(rho_i,rho_j) <= 1/(2m)
--
-- for every pair, not only the diagonal.  Therefore any nonnegative amplitude
-- a(D) satisfying
--
--   Re<D_i,D_j> <= a(D_i) a(D_j)
--
-- yields
--
--   offDiagonal <= (1/(2m)) (sum_i a(D_i))^2.
--
-- This is the exact finite positive-endpoint producer.  No incidence count is
-- introduced.  The only remaining physical input is the initial-data amplitude
-- sum on the literal companion family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact as R447
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNFiniteInitialCoherentEndpointRound460Exact as R460
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

two : ℚ
two = R449.two

record InitialCauchyAmplitudeData
    (floor : ℚ)
    (cells : List R446.PositiveRateComplex3Cell) : Set₁ where
  constructor initial-cauchy-amplitude-data
  field
    floorPositive : 0ℚ < floor
    floorBelowRate :
      (cell : R446.PositiveRateComplex3Cell) →
      floor ≤ R446.rate cell

    amplitude : R446.PositiveRateComplex3Cell → ℚ
    amplitudeNN :
      (cell : R446.PositiveRateComplex3Cell) →
      0ℚ ≤ amplitude cell

    hermitianCrossBelowAmplitudeProduct :
      (left right : R446.PositiveRateComplex3Cell) →
      R179.realHermitianCross (R446.value left) (R446.value right)
      ≤ amplitude left * amplitude right

open InitialCauchyAmplitudeData public

pairKernelBelowFloorCeiling :
  ∀ {floor cells}
    (P : InitialCauchyAmplitudeData floor cells)
    (left right : R446.PositiveRateComplex3Cell) →
  R446.cauchyKernel left right
  ≤ R449.diagonalCeilingAt floor (floorPositive P)
pairKernelBelowFloorCeiling {floor} P left right =
  let
    x = R446.rate left
    y = R446.rate right
    xPositive = ℚP.positive⁻¹ (R446.ratePositive left)
    yPositive = ℚP.positive⁻¹ (R446.ratePositive right)
    denominatorPositive = ℚP.+-mono-<-< xPositive yPositive
    lowerPositive = R449.twicePositive (floorPositive P)

    lowerSum : floor + floor ≤ x + y
    lowerSum = ℚP.+-mono-≤ (floorBelowRate P left) (floorBelowRate P right)

    lowerMeaning : floor + floor ≡ two * floor
    lowerMeaning = solve (floor ∷ [])

    lower : two * floor ≤ x + y
    lower = subst (_≤ x + y) lowerMeaning lowerSum

    asPositiveReciprocal :
      R446.cauchyKernel left right
      ≡ Quotient.positiveReciprocal (x + y) denominatorPositive
    asPositiveReciprocal =
      R449.safeReciprocalIsPositiveReciprocal (x + y) denominatorPositive

    antitone :
      Quotient.positiveReciprocal (x + y) denominatorPositive
      ≤ Quotient.positiveReciprocal (two * floor) lowerPositive
    antitone =
      Quotient.reciprocalAntitonePositive
        (two * floor) (x + y)
        lowerPositive denominatorPositive lower
  in
  subst
    (λ selected → selected ≤ R449.diagonalCeilingAt floor (floorPositive P))
    (sym asPositiveReciprocal)
    antitone

pairKernelNN :
  (left right : R446.PositiveRateComplex3Cell) →
  0ℚ ≤ R446.cauchyKernel left right
pairKernelNN left right =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (R443.cauchyEntryPositive
        (R446.rate left) (R446.rate right)
        (R446.ratePositive left) (R446.ratePositive right)))

literalPairFlux :
  R446.PositiveRateComplex3Cell →
  R446.PositiveRateComplex3Cell → ℚ
literalPairFlux left right =
  two * R446.cauchyKernel left right
    * R179.realHermitianCross (R446.value left) (R446.value right)

compileInitialEndpoint :
  ∀ {floor cells} →
  (P : InitialCauchyAmplitudeData floor cells) →
  R460.FiniteInitialCoherentEndpoint R446.PositiveRateComplex3Cell
compileInitialEndpoint {floor} P =
  R460.finite-initial-coherent-endpoint
    (amplitude P)
    literalPairFlux
    (R449.diagonalCeilingAt floor (floorPositive P))
    ceilingNN
    (amplitudeNN P)
    pairBound
  where
  ceilingNN : 0ℚ ≤ R449.diagonalCeilingAt floor (floorPositive P)
  ceilingNN =
    ℚP.<⇒≤
      (Quotient.positiveReciprocalPositive
        (two * floor) (R449.twicePositive (floorPositive P)))

  pairBound :
    (left right : R446.PositiveRateComplex3Cell) →
    literalPairFlux left right
    ≤
    R460.two * R449.diagonalCeilingAt floor (floorPositive P)
      * (amplitude P left * amplitude P right)
  pairBound left right =
    let
      K = R446.cauchyKernel left right
      W = R449.diagonalCeilingAt floor (floorPositive P)
      cross = R179.realHermitianCross (R446.value left) (R446.value right)
      product = amplitude P left * amplitude P right

      KNN = pairKernelNN left right
      productNN : 0ℚ ≤ product
      productNN =
        let
          instance leftNNI : NonNegative (amplitude P left)
          leftNNI = nonNegative (amplitudeNN P left)
          instance rightNNI : NonNegative (amplitude P right)
          rightNNI = nonNegative (amplitudeNN P right)
          instance productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            (amplitude P left) (amplitude P right)
        in ℚP.nonNegative⁻¹ product

      crossStep : K * cross ≤ K * product
      crossStep = ℚP.*-monoˡ-≤-nonNeg K
        (hermitianCrossBelowAmplitudeProduct P left right)
        {{nonNegative KNN}}

      kernelStep : K * product ≤ W * product
      kernelStep = ℚP.*-monoʳ-≤-nonNeg product
        (pairKernelBelowFloorCeiling P left right)
        {{nonNegative productNN}}

      core = ℚP.≤-trans crossStep kernelStep
      twoNN = ℚP.<⇒≤ R449.twoPositive
      scaled = ℚP.*-monoˡ-≤-nonNeg two core {{nonNegative twoNN}}
    in
    subst
      (λ upper → literalPairFlux left right ≤ upper)
      (solve (W ∷ product ∷ []))
      scaled

compiledOffDiagonalIsR447OffDiagonal :
  ∀ {floor cells}
    (P : InitialCauchyAmplitudeData floor cells) →
  R460.offDiagonalFlux (compileInitialEndpoint P) cells
  ≡ R447.offDiagonalForm cells
compiledOffDiagonalIsR447OffDiagonal P {cells = []} = refl
compiledOffDiagonalIsR447OffDiagonal P {cells = head ∷ rest} =
  cong₂ _+_
    (headExact head rest)
    (compiledOffDiagonalIsR447OffDiagonal P {cells = rest})
  where
  headExact :
    (selected : R446.PositiveRateComplex3Cell) →
    (tail : List R446.PositiveRateComplex3Cell) →
    R460.headPairFlux (compileInitialEndpoint P) selected tail
    ≡ R447.offDiagonalRow selected tail
  headExact selected [] = refl
  headExact selected (next ∷ tail) =
    cong₂ _+_ refl (headExact selected tail)

r447OffDiagonalBelowInitialAmplitudeSquare :
  ∀ {floor cells}
    (P : InitialCauchyAmplitudeData floor cells) →
  R447.offDiagonalForm cells
  ≤
  R449.diagonalCeilingAt floor (floorPositive P)
    * (R460.sumAmplitude (compileInitialEndpoint P) cells
      * R460.sumAmplitude (compileInitialEndpoint P) cells)
r447OffDiagonalBelowInitialAmplitudeSquare P =
  subst
    (λ selected → selected ≤
      R449.diagonalCeilingAt _ (floorPositive P)
        * (R460.sumAmplitude (compileInitialEndpoint P) _
          * R460.sumAmplitude (compileInitialEndpoint P) _))
    (compiledOffDiagonalIsR447OffDiagonal P)
    (R460.offDiagonalBelowAmplitudeSquare (compileInitialEndpoint P) _)

round461LiteralR447PositiveEndpointReducedToAmplitudeSquare : Bool
round461LiteralR447PositiveEndpointReducedToAmplitudeSquare = true

round461IntroducesCardinalityTax : Bool
round461IntroducesCardinalityTax = false

round461RequiresInitialAmplitudeSumProducer : Bool
round461RequiresInitialAmplitudeSumProducer = true

round461ContainsPostulate : Bool
round461ContainsPostulate = false

round461PackageAClosed : Bool
round461PackageAClosed = false

round461ClayPromotion : Bool
round461ClayPromotion = false

round461IntroducesCardinalityTaxIsFalse :
  round461IntroducesCardinalityTax ≡ false
round461IntroducesCardinalityTaxIsFalse = refl

round461ContainsPostulateIsFalse :
  round461ContainsPostulate ≡ false
round461ContainsPostulateIsFalse = refl
