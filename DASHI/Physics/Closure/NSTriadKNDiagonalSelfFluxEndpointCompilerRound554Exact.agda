module DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxEndpointCompilerRound554Exact where

------------------------------------------------------------------------
-- ROUND554 / SELF-FLUX ENDPOINT COMPILER FROM R549 + R457
--
-- R549 proves literalSelfFlux = 2 * R447.diagonal.
-- R457 bounds the same R447 diagonal by the exact energy-square endpoint.
-- This owner additionally proves R447.diagonal >= 0 directly from positivity
-- of each Cauchy entry and self-Hermitian mass.  Thus the self-flux endpoint is
-- nonnegative and has an explicit energy-square upper bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact as R447
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxToR447Round549Exact as R549

F : C3.RealField _
F = Rational.rationalRealField

diagonalFormNonnegative :
  (cells : List R446.PositiveRateComplex3Cell) →
  0ℚ ≤ R447.diagonalForm cells
diagonalFormNonnegative [] = ℚP.≤-refl
diagonalFormNonnegative (cell ∷ rest) =
  let
    entry = R446.cauchyKernel cell cell
    cross =
      DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact.realHermitianCross
        (R446.value cell) (R446.value cell)

    entryPositive = R443.cauchyEntryPositive
      (R446.rate cell) (R446.rate cell)
      (R446.ratePositive cell) (R446.ratePositive cell)
    entryNN = ℚP.<⇒≤ (ℚP.positive⁻¹ entry)
    crossNN = R451.selfHermitianNonnegative (R446.value cell)

    productNN : 0ℚ ≤ entry * cross
    productNN =
      let
        instance
          entryNNI : NonNegative entry
          entryNNI = nonNegative entryNN
          crossNNI : NonNegative cross
          crossNNI = nonNegative crossNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg entry cross
      in ℚP.nonNegative⁻¹ (entry * cross)
  in
  Rational.addNonnegative productNN (diagonalFormNonnegative rest)

module Endpoint
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R456.PhysicalModeRadiusCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Flux = R549.PhysicalSelfFlux
    physicalSystem S viscosityPositive cutoff output outputNonzero
  module Energy = R457.PhysicalDiagonalEndpoint
    physicalSystem S L H viscosityPositive unitGap radiusCalibration
    cutoff output outputNonzero

  diagonalNonnegative : 0ℚ ≤ Flux.Completion.diagonal
  diagonalNonnegative = diagonalFormNonnegative Flux.Completion.physicalCells

  twoNonnegative : 0ℚ ≤ R549.two
  twoNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ R549.two)

  literalSelfFluxNonnegative : 0ℚ ≤ Flux.literalSelfFluxSum
  literalSelfFluxNonnegative =
    let
      productNN : 0ℚ ≤ R549.two * Flux.Completion.diagonal
      productNN =
        let
          instance
            twoNNI : NonNegative R549.two
            twoNNI = nonNegative twoNonnegative
            diagNNI : NonNegative Flux.Completion.diagonal
            diagNNI = nonNegative diagonalNonnegative
            productNNI = ℚP.nonNeg*nonNeg⇒nonNeg R549.two Flux.Completion.diagonal
        in ℚP.nonNegative⁻¹ _
    in
    subst (0ℚ ≤_) (sym Flux.literalSelfFluxIsTwiceR447Diagonal) productNN

  selfFluxEnergySquareUpper :
    (P : Energy.PhysicalHelicityReceipt) →
    Flux.literalSelfFluxSum
    ≤ R549.two *
      (Energy.Diag.Floor.diagonalCeilingAt
        (Field30.viscosity physicalSystem)
        Energy.Diag.Floor.nuPositive
       * (DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact.fortyEight
          * Energy.energySquare))
  selfFluxEnergySquareUpper P =
    let
      diagonalUpper = Energy.r447DiagonalEnergySquareEndpoint P
      scaledUpper :
        R549.two * Flux.Completion.diagonal
        ≤ R549.two *
          (Energy.Diag.Floor.diagonalCeilingAt
            (Field30.viscosity physicalSystem)
            Energy.Diag.Floor.nuPositive
           * (DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact.fortyEight
              * Energy.energySquare))
      scaledUpper =
        let instance twoNN = nonNegative twoNonnegative
        in ℚP.*-monoˡ-≤-nonNeg R549.two diagonalUpper
    in
    subst
      (λ lower → lower ≤
        R549.two *
          (Energy.Diag.Floor.diagonalCeilingAt
            (Field30.viscosity physicalSystem)
            Energy.Diag.Floor.nuPositive
           * (DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact.fortyEight
              * Energy.energySquare)))
      Flux.literalSelfFluxIsTwiceR447Diagonal
      scaledUpper

round554SelfFluxNonnegativeClosed : Bool
round554SelfFluxNonnegativeClosed = true

round554SelfFluxEnergySquareEndpointClosed : Bool
round554SelfFluxEnergySquareEndpointClosed = true

round554IntroducesCardinalityTax : Bool
round554IntroducesCardinalityTax = false

round554FactoredFullSpacetimeBoundClosed : Bool
round554FactoredFullSpacetimeBoundClosed = false

round554ClayPromotion : Bool
round554ClayPromotion = false

round554SelfFluxEnergySquareEndpointClosedIsTrue :
  round554SelfFluxEnergySquareEndpointClosed ≡ true
round554SelfFluxEnergySquareEndpointClosedIsTrue = refl

round554ClayPromotionIsFalse : round554ClayPromotion ≡ false
round554ClayPromotionIsFalse = refl
