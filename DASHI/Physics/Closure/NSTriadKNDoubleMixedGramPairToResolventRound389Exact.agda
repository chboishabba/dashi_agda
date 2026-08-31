module DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact where

------------------------------------------------------------------------
-- ROUND389 / LITERAL DOUBLE-MIXED GRAM PAIR -> R290 RESOLVENT PAIR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (Positive)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNRationalResolventFromPositiveGramPairRound384Exact as R384
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225

F : C3.RealField _
F = Rational.rationalRealField

module DoubleMixedPair
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module D = R388.PhysicalDoubleMixed physicalSystem S

  physicalDoubleMixedPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    R291.DampedCellPair
  physicalDoubleMixedPair alpha beta = record
    { R291.cellA = R225.doubleMixedCell S D.Pair.velocity alpha
    ; R291.cellB = R225.doubleMixedCell S D.Pair.velocity beta
    ; R291.tangentA = D.doubleTangent alpha
    ; R291.tangentB = D.doubleTangent beta
    ; R291.forcingA = D.doubleForcing alpha
    ; R291.forcingB = D.doubleForcing beta
    ; R291.rateA = D.Pair.cellRate alpha
    ; R291.rateB = D.Pair.cellRate beta
    ; R291.tangentALaw = D.doubleMixedDampedTangent alpha
    ; R291.tangentBLaw = D.doubleMixedDampedTangent beta
    }

  pairRatePositiveBuildsR290 :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (physicalDoubleMixedPair alpha beta)) →
    R290.DampedGramPair
  pairRatePositiveBuildsR290 alpha beta positive =
    R384.positivePairBuildsR290
      (physicalDoubleMixedPair alpha beta) positive

round389LiteralR378CarrierPairReachesR290 : Bool
round389LiteralR378CarrierPairReachesR290 = true

round389NonlinearRemainderSignAssumed : Bool
round389NonlinearRemainderSignAssumed = false

round389OnlyLocalUnpaidPremiseIsPairRatePositivity : Bool
round389OnlyLocalUnpaidPremiseIsPairRatePositivity = true

round389LiteralR378CarrierPairReachesR290IsTrue :
  round389LiteralR378CarrierPairReachesR290 ≡ true
round389LiteralR378CarrierPairReachesR290IsTrue = refl
