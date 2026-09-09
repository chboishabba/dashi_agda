module DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalSelfGramEnergyControlRound550Exact where

------------------------------------------------------------------------
-- ROUND550 / R549 SELF-GRAM TERM -> EXISTING PHYSICAL ENERGY-SQUARE CONTROL
--
-- R549 resolves the literal R547 diagonal as
--
--   Diagonal = SelfGram + WeightedGramFluxTangent.
--
-- This owner reuses the already-proved physical infrastructure rather than
-- introducing another diagonal estimate:
--
--   * R400 constructs positive cell/pair rates on every nonzero physical output
--     fibre;
--   * R457 identifies self-Hermitian mass with the Euclidean C^3 norm;
--   * R456 bounds the sum of literal double-mixed masses by 48 E_N^2.
--
-- Consequently the SelfGram part is exactly twice the existing double-mixed
-- mass sum and inherits a cutoff-independent energy-square bound.  The only
-- remaining diagonal coordinate is the weighted Gram-flux tangent, whose time
-- integration/endpoint realization remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (Positive; nonNegative)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalR290FluxDecompositionRound549Exact as R549
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module SelfGram
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  module D = R549.Diagonal physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  velocity : Z3.FourierMode → C3.Complex3 F
  velocity = D.Pair.D.Pair.velocity

  doubleMixedValue : Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleMixedValue tau = R225.doubleMixedCell S velocity tau

  ----------------------------------------------------------------------
  -- 1. R400 constructs the self-pair positivity that R549 deliberately kept
  -- separate from the off-diagonal R396 carrier.
  ----------------------------------------------------------------------

  buildSelfRatePositiveOn550 :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    D.SelfRatePositiveOn549 items
  buildSelfRatePositiveOn550 output outputNonzero [] allOutput =
    D.selfPositiveNil549
  buildSelfRatePositiveOn550 output outputNonzero (alpha ∷ rest) allOutput =
    D.selfPositiveCons549 alphaSelfPositive tailPositive
    where
    alphaCellPositive : Positive (D.Pair.D.Pair.cellRate alpha)
    alphaCellPositive =
      Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha (allOutput alpha R396.here)

    alphaSelfPositive :
      Positive (R291.pairRate (D.Pair.physicalDoubleMixedPair alpha alpha))
    alphaSelfPositive =
      Rate.pairRatePositiveFromCellRates
        alpha alpha alphaCellPositive alphaCellPositive

    tailPositive : D.SelfRatePositiveOn549 rest
    tailPositive =
      buildSelfRatePositiveOn550 output outputNonzero rest
        (λ tau member → allOutput tau (R396.there member))

  physicalOutputSelfRatePositive550 :
    (cutoff : Nat) (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    D.SelfRatePositiveOn549 (Output.physicalOutputFiber cutoff output)
  physicalOutputSelfRatePositive550 cutoff output outputNonzero =
    buildSelfRatePositiveOn550 output outputNonzero
      (Output.physicalOutputFiber cutoff output)
      (Rate.allElementsHaveOutput cutoff output)

  ----------------------------------------------------------------------
  -- 2. SelfGram is exactly twice the already-owned physical mass sum.
  ----------------------------------------------------------------------

  selfGramPointwiseIsTwoMass550 :
    (alpha : Physical.PhysicalTriadIncidence) →
    (positive : Positive
      (R291.pairRate (D.Pair.physicalDoubleMixedPair alpha alpha))) →
    R290.gram (D.selfPair alpha positive)
    ≡ R291.two * R456.norm (doubleMixedValue alpha)
  selfGramPointwiseIsTwoMass550 alpha positive
    rewrite R457.selfHermitianIsNorm (doubleMixedValue alpha) = refl

  selfGramSumIsTwoPhysicalMass550 :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : D.SelfRatePositiveOn549 items) →
    D.selfGramSum549 items positive
    ≡ R291.two * R456.sumDoubleMixedMass S velocity items
  selfGramSumIsTwoPhysicalMass550 [] D.selfPositiveNil549 = refl
  selfGramSumIsTwoPhysicalMass550
      (alpha ∷ rest) (D.selfPositiveCons549 positive tailPositive)
    rewrite selfGramPointwiseIsTwoMass550 alpha positive
          | selfGramSumIsTwoPhysicalMass550 rest tailPositive =
    solve
      (R456.norm (doubleMixedValue alpha)
        ∷ R456.sumDoubleMixedMass S velocity rest
        ∷ [])

  ----------------------------------------------------------------------
  -- 3. Existing R456 bound transports directly to SelfGram.
  ----------------------------------------------------------------------

  twoNonnegative550 : 0ℚ ≤ R291.two
  twoNonnegative550 =
    Rational.addNonnegative
      (Rational.squareNonnegative 1ℚ)
      (Rational.squareNonnegative 1ℚ)

  fixedOutputSelfGramBelowEnergySquare550 :
    (L : Helical.PeriodicHelicalProjectorLaws
      F (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S) →
    (H : R142.HelicalHalfCalibration S) →
    (radiusCalibration :
      R456.PhysicalModeRadiusCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S) →
    (helicity :
      R225.PhysicalFixedOutputHelicityData
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S L H velocity) →
    (cutoff : Nat) (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    let positive = physicalOutputSelfRatePositive550 cutoff output outputNonzero
        energy = R453.sumEnergy
          (R456.physicalModalEnergy velocity) (Cube.cutoffModes cutoff)
    in
    D.selfGramSum549 (Output.physicalOutputFiber cutoff output) positive
    ≤ R291.two * (R452.fortyEight * (energy * energy))
  fixedOutputSelfGramBelowEnergySquare550
      L H radiusCalibration helicity cutoff output outputNonzero =
    let
      fibre = Output.physicalOutputFiber cutoff output
      positive = physicalOutputSelfRatePositive550 cutoff output outputNonzero
      energy = R453.sumEnergy
        (R456.physicalModalEnergy velocity) (Cube.cutoffModes cutoff)

      massBound :
        R456.sumDoubleMixedMass S velocity fibre
        ≤ R452.fortyEight * (energy * energy)
      massBound =
        R456.fixedOutputDoubleMixedMassBelowEnergySquare
          helicity radiusCalibration cutoff output

      instance twoNNI = nonNegative twoNonnegative550

      scaled :
        R291.two * R456.sumDoubleMixedMass S velocity fibre
        ≤ R291.two * (R452.fortyEight * (energy * energy))
      scaled = ℚP.*-monoˡ-≤-nonNeg R291.two massBound
    in
    subst
      (λ lower → lower ≤ R291.two * (R452.fortyEight * (energy * energy)))
      (sym (selfGramSumIsTwoPhysicalMass550 fibre positive))
      scaled

------------------------------------------------------------------------
-- 4. Status.
------------------------------------------------------------------------

round550PhysicalSelfPairPositivityConstructed : Bool
round550PhysicalSelfPairPositivityConstructed = true

round550SelfGramExactPhysicalMassWeldClosed : Bool
round550SelfGramExactPhysicalMassWeldClosed = true

round550SelfGramEnergySquareControlClosed : Bool
round550SelfGramEnergySquareControlClosed = true

round550IntroducesCardinalityTax : Bool
round550IntroducesCardinalityTax = false

round550WeightedFluxTangentEndpointClosed : Bool
round550WeightedFluxTangentEndpointClosed = false

round550LiteralR406SignedCrossPaymentClosed : Bool
round550LiteralR406SignedCrossPaymentClosed = false

round550CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round550CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round550ClayPromotion : Bool
round550ClayPromotion = false

round550PhysicalSelfPairPositivityConstructedIsTrue :
  round550PhysicalSelfPairPositivityConstructed ≡ true
round550PhysicalSelfPairPositivityConstructedIsTrue = refl

round550SelfGramEnergySquareControlClosedIsTrue :
  round550SelfGramEnergySquareControlClosed ≡ true
round550SelfGramEnergySquareControlClosedIsTrue = refl

round550IntroducesCardinalityTaxIsFalse :
  round550IntroducesCardinalityTax ≡ false
round550IntroducesCardinalityTaxIsFalse = refl

round550ClayPromotionIsFalse : round550ClayPromotion ≡ false
round550ClayPromotionIsFalse = refl
