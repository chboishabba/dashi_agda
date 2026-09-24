{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateLiftedDynamicCancellationRound688Exact where

------------------------------------------------------------------------
-- ROUND688 / C2 IS A DEGREE-FOUR CANCELLATION INSIDE THE RATE-LIFTED R568 PAIR
--
-- R687:
--
--   RateLiftedFull = 8 W(M,C).
--
-- R685:
--
--   WeightedWork = W(M,C) - W(M,T).
--
-- Therefore, on the SAME nonzero physical fixed-output fibre,
--
--   RateLiftedFull - 8 W(M,T) = 8 WeightedWork.
--
-- The two terms on the left both contain the nonlinear forcing/tangent
-- contribution.  Their difference is the physical viscous rate kernel on the
-- right.  This identity is the firewall against estimating the quintic
-- commutator and tangent pieces independently when proving C2.
--
-- No inequality, norm, absolute value, or new Clay leaf is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; Positive; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as PhysicalRate
import DASHI.Physics.Closure.NSTriadKNR650RateKernelCommutatorEndpointRound685Exact as R685
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Lift =
    R687.FixedOutput physicalSystem S viscosityPositive output outputNonzero

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  velocity = Audit.velocityAt system
  forcing = Audit.projectedNonlinearity system
  rho = R94.physicalDecayRate physicalSystem

  items = Output.physicalOutputFiber cutoff output
  value = D1a.mixedProductCell S velocity
  mixed = R224.foldVector value items
  work = Pair.cellWork mixed value

  weightedWork : ℚ
  weightedWork =
    Pair.weightedWorkSum
      (PhysicalRate.physicalCellRate physicalSystem)
      work
      items

  tangent =
    Work.fixedOutputDampedTangent rho S velocity forcing cutoff output

  tangentWork : ℚ
  tangentWork = Work.coherentWork mixed tangent

  commutatorWork : ℚ
  commutatorWork = Work.coherentWork mixed Lift.commutator

  rateLiftedFull : ℚ
  rateLiftedFull =
    R543.fullSquareSum Lift.liftedForcingPair Lift.fibre

  weightedIsCommutatorMinusTangent :
    weightedWork ≡ commutatorWork - tangentWork
  weightedIsCommutatorMinusTangent =
    R685.fixedOutputPhysicalRateKernelIsCommutatorMinusTangent
      physicalSystem S output

  rateLiftedIsEightCommutator :
    rateLiftedFull ≡ R687.eight * commutatorWork
  rateLiftedIsEightCommutator =
    Lift.liftedForcingFullIsEightCommutatorWork

  rateLiftedMinusTangentIsEightWeighted :
    rateLiftedFull - R687.eight * tangentWork
    ≡ R687.eight * weightedWork
  rateLiftedMinusTangentIsEightWeighted =
    trans
      (cong
        (λ selected → selected - R687.eight * tangentWork)
        rateLiftedIsEightCommutator)
      (trans
        (solve
          ( R687.eight
          ∷ commutatorWork
          ∷ tangentWork
          ∷ []))
        (cong (R687.eight *_) (sym weightedIsCommutatorMinusTangent)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round688RateLiftedMinusTangentIsEightPhysicalRateKernel : Bool
round688RateLiftedMinusTangentIsEightPhysicalRateKernel = true

round688C2RequiresSeparateRateLiftedAndTangentUpperBounds : Bool
round688C2RequiresSeparateRateLiftedAndTangentUpperBounds = false

round688C2PreferredSignedObjectPreservesDynamicCancellation : Bool
round688C2PreferredSignedObjectPreservesDynamicCancellation = true

round688IntroducesEstimate : Bool
round688IntroducesEstimate = false

round688SignedDynamicCancellationQuantitativePaymentClosed : Bool
round688SignedDynamicCancellationQuantitativePaymentClosed = false

round688C2Closed : Bool
round688C2Closed = false

round688IntroducesNewClayLeaf : Bool
round688IntroducesNewClayLeaf = false

round688ClayPromotion : Bool
round688ClayPromotion = false
