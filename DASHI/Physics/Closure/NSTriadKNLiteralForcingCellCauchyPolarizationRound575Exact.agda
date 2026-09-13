module DASHI.Physics.Closure.NSTriadKNLiteralForcingCellCauchyPolarizationRound575Exact where

------------------------------------------------------------------------
-- ROUND575 / LITERAL R567 FORCING SQUARE -> R446 CAUCHY POLARIZATION
--
-- On one physical nonzero output fibre set
--
--   G_tau = literal R388 doubleForcing tau,
--   D_tau = literal R225 doubleMixedCell tau,
--   rate_tau = physical viscous cell rate.
--
-- The R574 mixed Cauchy pair is exactly R566's forcingPair.  Therefore
--
--   2 forcingFull_k <= forcingQuadratic_k + cellQuadratic_k.
--
-- This is an alternative producer reduction only.  The next BIDI audit must
-- decide whether the two positive quadratics are actually cheaper to control.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNCauchyPolarizationUpperRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalPolarization
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module T = R566.PhysicalTranspose physicalSystem S

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  doubleCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleCell tau = R225.doubleMixedCell S D.Pair.velocity tau

  cell575 :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    R574.CauchyVectorPairCell574
  cell575 tau outputExact =
    R574.cauchy-vector-pair-cell-574
      (D.Pair.cellRate tau)
      (D.doubleForcing tau)
      (doubleCell tau)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero tau outputExact)

  buildCells575 :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    List R574.CauchyVectorPairCell574
  buildCells575 [] allOutput = []
  buildCells575 (tau ∷ rest) allOutput =
    cell575 tau (allOutput tau R396.here)
    ∷ buildCells575 rest
        (λ selected member → allOutput selected (R396.there member))

  cells575 : List R574.CauchyVectorPairCell574
  cells575 = buildCells575 fibre (Rate.allElementsHaveOutput cutoff output)

  forcingQuadratic575 : ℚ
  forcingQuadratic575 = R543.fullSquareSum R574.leftPair574 cells575

  cellQuadratic575 : ℚ
  cellQuadratic575 = R543.fullSquareSum R574.rightPair574 cells575

  pairMixedExact575 :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    R574.mixedPair574 (cell575 alpha alphaOutput) (cell575 beta betaOutput)
    ≡ T.forcingPair alpha beta
  pairMixedExact575 alpha beta alphaOutput betaOutput =
    sym (T.forcingPairScalarized alpha beta)

  mixedRowExact575 :
    (head : Physical.PhysicalTriadIncidence) →
    (headOutput : Physical.k head ≡ output) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (restOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn rest → Physical.k tau ≡ output) →
    R539.rowSum R574.mixedPair574
      (cell575 head headOutput) (buildCells575 rest restOutput)
    ≡ R539.rowSum T.forcingPair head rest
  mixedRowExact575 head headOutput [] restOutput = refl
  mixedRowExact575 head headOutput (beta ∷ rest) restOutput =
    cong₂ _+_
      (pairMixedExact575 head beta headOutput (restOutput beta R396.here))
      (mixedRowExact575 head headOutput rest
        (λ selected member → restOutput selected (R396.there member)))

  mixedColumnExact575 :
    (rest : List Physical.PhysicalTriadIncidence) →
    (restOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn rest → Physical.k tau ≡ output) →
    (head : Physical.PhysicalTriadIncidence) →
    (headOutput : Physical.k head ≡ output) →
    R539.columnSum R574.mixedPair574
      (buildCells575 rest restOutput) (cell575 head headOutput)
    ≡ R539.columnSum T.forcingPair rest head
  mixedColumnExact575 [] restOutput head headOutput = refl
  mixedColumnExact575 (beta ∷ rest) restOutput head headOutput =
    cong₂ _+_
      (pairMixedExact575 beta head (restOutput beta R396.here) headOutput)
      (mixedColumnExact575 rest
        (λ selected member → restOutput selected (R396.there member))
        head headOutput)

  mixedFullExact575 :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    R543.fullSquareSum R574.mixedPair574 (buildCells575 items allOutput)
    ≡ R543.fullSquareSum T.forcingPair items
  mixedFullExact575 [] allOutput = refl
  mixedFullExact575 (head ∷ rest) allOutput
    rewrite pairMixedExact575 head head
      (allOutput head R396.here) (allOutput head R396.here)
          | mixedRowExact575 head (allOutput head R396.here) rest
              (λ selected member → allOutput selected (R396.there member))
          | mixedColumnExact575 rest
              (λ selected member → allOutput selected (R396.there member))
              head (allOutput head R396.here)
          | mixedFullExact575 rest
              (λ selected member → allOutput selected (R396.there member)) = refl

  physicalForcingPolarizationUpper575 :
    R573.two573 * R543.fullSquareSum T.forcingPair fibre
    ≤ forcingQuadratic575 + cellQuadratic575
  physicalForcingPolarizationUpper575 =
    subst
      (λ mixed →
        R573.two573 * mixed ≤ forcingQuadratic575 + cellQuadratic575)
      (mixedFullExact575 fibre (Rate.allElementsHaveOutput cutoff output))
      (R574.mixedCauchyPolarizationUpper574 cells575)

round575LiteralForcingHalfAttachedToR446Polarization : Bool
round575LiteralForcingHalfAttachedToR446Polarization = true

round575ForcingFullUpperByTwoPositiveQuadratics : Bool
round575ForcingFullUpperByTwoPositiveQuadratics = true

round575ForcingQuadraticCutoffUniformSpacetimePaid : Bool
round575ForcingQuadraticCutoffUniformSpacetimePaid = false

round575CellQuadraticCutoffUniformSpacetimePaid : Bool
round575CellQuadraticCutoffUniformSpacetimePaid = false

round575PolarizationDeclaredShortestRoute : Bool
round575PolarizationDeclaredShortestRoute = false

round575CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round575CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round575ClayPromotion : Bool
round575ClayPromotion = false

round575ClayPromotionIsFalse : round575ClayPromotion ≡ false
round575ClayPromotionIsFalse = refl
