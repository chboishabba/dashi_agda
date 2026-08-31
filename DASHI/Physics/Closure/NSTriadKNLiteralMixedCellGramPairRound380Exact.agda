module DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairRound380Exact where

------------------------------------------------------------------------
-- ROUND380 / BIDI: R94 LITERAL COEFFICIENT -> R292 CELL -> R291 GRAM PAIR
--
-- Round94 already identifies the literal finite Navier--Stokes coefficient
-- definitionally as
--
--   - rho(k) u(k) + N(u)(k),   rho(k) = nu |k|^2.
--
-- Round292 needs exactly this damped-forced modal shape to differentiate the
-- literal R224 mixed-helicity cell.  Round291 then differentiates the exact
-- R179 real-Hermitian Gram scalar of two such cells.
--
-- We deliberately avoid function extensionality.  The canonical tangent below
-- is built from the damped-forced function itself, while the pointwise receipt
-- shows that at every physical mode it is the SAME value as the repository's
-- literal R94/R30 coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Damped
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292

F : C3.RealField _
F = Rational.rationalRealField

module LiteralPair
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (projectorLinearity :
      R292.HelicalDampedProjectorLinearity
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem

  velocity : Z3.FourierMode → C3.Complex3 F
  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)

  forcing : Z3.FourierMode → C3.Complex3 F
  forcing = Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem)

  rho : Z3.FourierMode → ℚ
  rho = R94.physicalDecayRate physicalSystem

  dampedCoefficient : Z3.FourierMode → C3.Complex3 F
  dampedCoefficient mode =
    Damped.dampedPlusForcing (rho mode) (velocity mode) (forcing mode)

  literalCoefficient : Z3.FourierMode → C3.Complex3 F
  literalCoefficient = Field30.literalViscousQuadraticCoefficient physicalSystem

  literalCoefficientIsDamped :
    (mode : Z3.FourierMode) →
    literalCoefficient mode ≡ dampedCoefficient mode
  literalCoefficientIsDamped = R94.literalCoefficientIsDampedPlusNetwork physicalSystem

  mixedCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedCell = R224.mixedPlusMinus {E = E} {I = I} S velocity

  mixedCellTangent : Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedCellTangent = R292.cellTangent S velocity dampedCoefficient

  mixedCellForcing : Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedCellForcing = R230.productRuleForcingCell S velocity forcing

  cellRate : Physical.PhysicalTriadIncidence → ℚ
  cellRate tau = rho (Physical.p tau) + rho (Physical.q tau)

  mixedCellDampedLaw :
    (tau : Physical.PhysicalTriadIncidence) →
    mixedCellTangent tau
    ≡ C3.complex3Add
        (C3.complex3Scale
          (Damped.negativeReal (cellRate tau))
          (mixedCell tau))
        (mixedCellForcing tau)
  mixedCellDampedLaw tau =
    R292.mixedCellDampedTangent
      S projectorLinearity velocity forcing rho tau

  physicalDampedCellPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    R291.DampedCellPair
  physicalDampedCellPair alpha beta = record
    { R291.cellA = mixedCell alpha
    ; R291.cellB = mixedCell beta
    ; R291.tangentA = mixedCellTangent alpha
    ; R291.tangentB = mixedCellTangent beta
    ; R291.forcingA = mixedCellForcing alpha
    ; R291.forcingB = mixedCellForcing beta
    ; R291.rateA = cellRate alpha
    ; R291.rateB = cellRate beta
    ; R291.tangentALaw = mixedCellDampedLaw alpha
    ; R291.tangentBLaw = mixedCellDampedLaw beta
    }

  physicalGramPairTangent :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R291.gramTangent (physicalDampedCellPair alpha beta)
    ≡
    (0ℚ - R291.pairRate (physicalDampedCellPair alpha beta))
      * R291.gram (physicalDampedCellPair alpha beta)
      + R291.nonlinearGramRemainder (physicalDampedCellPair alpha beta)
  physicalGramPairTangent alpha beta =
    R291.gramPairDampedTangent (physicalDampedCellPair alpha beta)

round380LiteralCoefficientPointwiseIdentified : Bool
round380LiteralCoefficientPointwiseIdentified = true

round380PhysicalR227CellDampedTangentClosedModuloProjectorLinearity : Bool
round380PhysicalR227CellDampedTangentClosedModuloProjectorLinearity = true

round380TwoCellR179GramTangentClosedModuloProjectorLinearity : Bool
round380TwoCellR179GramTangentClosedModuloProjectorLinearity = true

round380FiniteOffDiagonalAggregationClosed : Bool
round380FiniteOffDiagonalAggregationClosed = false

round380PackageAClosed : Bool
round380PackageAClosed = false

round380LiteralCoefficientPointwiseIdentifiedIsTrue :
  round380LiteralCoefficientPointwiseIdentified ≡ true
round380LiteralCoefficientPointwiseIdentifiedIsTrue = refl
