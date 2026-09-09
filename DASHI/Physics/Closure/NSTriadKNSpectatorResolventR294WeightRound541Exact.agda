module DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact where

------------------------------------------------------------------------
-- ROUND541 / FIXED-SPECTATOR CAUCHY RESOLVENT IS AN R294 CELL WEIGHT
--
-- The literal R406 pair kernel is nonseparable:
--
--   K(alpha,beta) = 1 / (lambda_alpha + lambda_beta).
--
-- Nonseparability does not obstruct the R294 p/q-swap collapse.  Fix beta and
-- regard
--
--   phi_beta(r) = 1 / (r + lambda_beta)
--
-- as a scalar function of alpha's ONE-cell damping rate.  R295 then constructs
-- an exact swap-invariant R294 weight.  On the physical R380/R388 carrier that
-- weight is the same reciprocal used by R538's proof-independent pair scalar.
--
-- No Laplace transform, exponential, norm, or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

module Spectator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  spectatorPhi :
    Physical.PhysicalTriadIncidence → ℚ → C3.Complex F
  spectatorPhi beta rate =
    C3.realEmbed F
      (Reciprocal.safeRationalReciprocal
        (rate + D.Pair.cellRate beta))

  spectatorWeight :
    Physical.PhysicalTriadIncidence → R294.SwapInvariantCellWeight F
  spectatorWeight beta =
    R295.rateFunctionBuildsR294Weight
      D.Pair.rho
      (spectatorPhi beta)

  spectatorWeightMeaning :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    R294.weight (spectatorWeight beta) alpha
    ≡ C3.realEmbed F (Swap.pairResolvent alpha beta)
  spectatorWeightMeaning beta alpha = refl

  spectatorWeightSwapInvariant :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    R294.weight (spectatorWeight beta)
      (DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry.swapTriad alpha)
    ≡ R294.weight (spectatorWeight beta) alpha
  spectatorWeightSwapInvariant beta alpha =
    R294.swapInvariant (spectatorWeight beta) alpha

round541SpectatorResolventBuildsR294Weight : Bool
round541SpectatorResolventBuildsR294Weight = true

round541SpectatorWeightIsLiteralPairResolvent : Bool
round541SpectatorWeightIsLiteralPairResolvent = true

round541LaplaceFactorizationRequired : Bool
round541LaplaceFactorizationRequired = false

round541FullRowCommutatorWeldClosed : Bool
round541FullRowCommutatorWeldClosed = false

round541SignedSpacetimeEstimateClosed : Bool
round541SignedSpacetimeEstimateClosed = false

round541ClayPromotion : Bool
round541ClayPromotion = false

round541SpectatorResolventBuildsR294WeightIsTrue :
  round541SpectatorResolventBuildsR294Weight ≡ true
round541SpectatorResolventBuildsR294WeightIsTrue = refl

round541LaplaceFactorizationRequiredIsFalse :
  round541LaplaceFactorizationRequired ≡ false
round541LaplaceFactorizationRequiredIsFalse = refl

round541ClayPromotionIsFalse : round541ClayPromotion ≡ false
round541ClayPromotionIsFalse = refl
