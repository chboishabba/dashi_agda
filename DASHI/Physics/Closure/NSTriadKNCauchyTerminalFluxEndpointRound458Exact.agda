module DASHI.Physics.Closure.NSTriadKNCauchyTerminalFluxEndpointRound458Exact where

------------------------------------------------------------------------
-- ROUND458 / CAUCHY COMPLETION PAYS THE NEGATIVE TERMINAL R397 FLUX
--
-- R447 proves
--
--   -offDiagonal <= diagonal.
--
-- R448 identifies that offDiagonal with the literal fixed-output R397/R385
-- weighted flux.  R457 now pays the diagonal by
--
--   diagonalCeiling(nu) * (48 E_N^2).
--
-- Therefore the endpoint orientation that appears in R393 as -F(T) has a
-- cutoff-independent same-object bound whenever the physical radius and
-- canonical Fourier calibrations are supplied.
--
-- This does NOT bound +F(T), and does not by itself pay the R423 spacetime
-- nonlinear remainder.  The one-sided orientation is recorded explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyOffDiagonalR397WeldRound448Exact as R448
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452

F : C3.RealField _
F = Rational.rationalRealField

module TerminalFluxEndpoint
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

  module D = R457.PhysicalDiagonalEndpoint
    physicalSystem S L H viscosityPositive unitGap radiusCalibration
    cutoff output outputNonzero

  PhysicalHelicityReceipt : Set
  PhysicalHelicityReceipt =
    R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H D.velocity

  module WithHelicity (Pdata : PhysicalHelicityReceipt) where

    module O = R448.PhysicalOffDiagonalWeld
      physicalSystem S L H Pdata viscosityPositive cutoff output outputNonzero

    terminalFlux : ℚ
    terminalFlux =
      R385.sumWeightedFlux
        (O.OutputFlux.outputPairs cutoff output O.pairPositive)

    terminalFluxIsOffDiagonal :
      terminalFlux ≡ D.Diag.Completion.offDiagonal
    terminalFluxIsOffDiagonal = sym O.r447OffDiagonalIsR397WeightedFlux

    negativeTerminalFluxPaidByDiagonal :
      0ℚ - terminalFlux ≤ D.Diag.Completion.diagonal
    negativeTerminalFluxPaidByDiagonal =
      subst
        (λ selected → 0ℚ - selected ≤ D.Diag.Completion.diagonal)
        terminalFluxIsOffDiagonal
        D.Diag.Completion.negativeOffDiagonalPaidByDiagonal

    negativeTerminalFluxEnergySquareEndpoint :
      0ℚ - terminalFlux
      ≤ R449.diagonalCeilingAt D.Diag.nu D.Diag.Floor.nuPositive
          * (R452.fortyEight * D.energySquare)
    negativeTerminalFluxEnergySquareEndpoint =
      ℚP.≤-trans
        negativeTerminalFluxPaidByDiagonal
        (D.r447DiagonalEnergySquareEndpoint Pdata)

round458NegativeTerminalR397FluxPaid : Bool
round458NegativeTerminalR397FluxPaid = true

round458PositiveTerminalR397FluxPaid : Bool
round458PositiveTerminalR397FluxPaid = false

round458SpacetimeRemainderPaid : Bool
round458SpacetimeRemainderPaid = false

round458IntroducesCardinalityTax : Bool
round458IntroducesCardinalityTax = false

round458ContainsPostulate : Bool
round458ContainsPostulate = false

round458PackageAClosed : Bool
round458PackageAClosed = false

round458ClayPromotion : Bool
round458ClayPromotion = false

round458PositiveTerminalR397FluxPaidIsFalse :
  round458PositiveTerminalR397FluxPaid ≡ false
round458PositiveTerminalR397FluxPaidIsFalse = refl

round458SpacetimeRemainderPaidIsFalse :
  round458SpacetimeRemainderPaid ≡ false
round458SpacetimeRemainderPaidIsFalse = refl
