module DASHI.Physics.Closure.NSTriadKNPeriodicSignedFrequencyCarrierRealizationExact where

------------------------------------------------------------------------
-- PERIODIC REALIZATION OF THE DOMAIN-INDEPENDENT SIGNED FREQUENCY CARRIER
--
-- This file proves that the literal fixed-output R290/R503 pair used by the
-- current periodic B lane inhabits the abstract carrier from
-- NSTriadKNSignedFrequencyCarrierExact.
--
-- For a positive physical double-mixed pair on one output fibre:
--
--   weightedFlux
--     = w_ab g_ab
--
--   commonResolventFlux
--     = w_k g_ab
--
--   centeredResolventCorrection
--     = w_ab w_k s_ab g_ab
--
-- and the existing theorem proves, without an estimate,
--
--   w_ab g_ab = w_k g_ab - w_ab w_k s_ab g_ab.
--
-- This is the portability quotient we want: the signed algebra is now a
-- theorem over a domain-independent carrier, while Z^3 incidence and the
-- finite fibre remain confined to this realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; _-_; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventCenteredDefectExact as Defect
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventGramFluxSplitExact as SplitOwner
import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core

F : C3.RealField _
F = Rational.rationalRealField

module PeriodicRealization
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode)
    (outputPositive :
      Positive
        (Defect.PhysicalResolventDefect.outputPairHeatRate
          physicalSystem S output)) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module D = Defect.PhysicalResolventDefect physicalSystem S
  module Split =
    SplitOwner.FixedOutputSplit
      physicalSystem S output outputPositive

  record PeriodicPairInteraction : Set where
    constructor periodic-pair-interaction
    field
      alpha : Physical.PhysicalTriadIncidence
      beta : Physical.PhysicalTriadIncidence
      alphaOutput : Physical.k alpha ≡ output
      betaOutput : Physical.k beta ≡ output
      pairPositive : Positive (D.physicalPairRate alpha beta)

  open PeriodicPairInteraction public

  dampedPair :
    PeriodicPairInteraction → R290.DampedGramPair
  dampedPair x =
    Pair.pairRatePositiveBuildsR290
      (alpha x) (beta x) (pairPositive x)

  periodicWeightedFlux :
    PeriodicPairInteraction → ℚ
  periodicWeightedFlux x =
    R290.weightedGramFlux (dampedPair x)

  periodicCommonResolventFlux :
    PeriodicPairInteraction → ℚ
  periodicCommonResolventFlux x =
    D.outputResolvent output * R290.gram (dampedPair x)

  periodicCenteredResolventCorrection :
    PeriodicPairInteraction → ℚ
  periodicCenteredResolventCorrection x =
    Split.pairCorrection
      (alpha x) (beta x) (pairPositive x)

  periodicPointwiseCenteredResolventSplit :
    (x : PeriodicPairInteraction) →
    periodicWeightedFlux x
    ≡
    periodicCommonResolventFlux x
      - periodicCenteredResolventCorrection x
  periodicPointwiseCenteredResolventSplit x =
    Split.pairWeightedFluxSplit
      (alpha x) (beta x)
      (alphaOutput x) (betaOutput x)
      (pairPositive x)

  periodicSignedFrequencyCarrier :
    Core.SignedFrequencyCarrier
  periodicSignedFrequencyCarrier = record
    { Interaction = PeriodicPairInteraction
    ; Scalar = ℚ
    ; _minus_ = _-_
    ; weightedFlux = periodicWeightedFlux
    ; commonResolventFlux = periodicCommonResolventFlux
    ; centeredResolventCorrection =
        periodicCenteredResolventCorrection
    ; pointwiseCenteredResolventSplit =
        periodicPointwiseCenteredResolventSplit
    }

  periodicCarrierWeightedFluxIsLiteralR290 :
    (x : PeriodicPairInteraction) →
    Core.weightedFlux periodicSignedFrequencyCarrier x
    ≡ R290.weightedGramFlux (dampedPair x)
  periodicCarrierWeightedFluxIsLiteralR290 x = refl

  periodicCarrierCorrectionIsExistingCenteredDefect :
    (x : PeriodicPairInteraction) →
    Core.centeredResolventCorrection periodicSignedFrequencyCarrier x
    ≡
    Split.pairCorrection
      (alpha x) (beta x) (pairPositive x)
  periodicCarrierCorrectionIsExistingCenteredDefect x = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

periodicSignedCarrierConcreteRealizationClosed : Bool
periodicSignedCarrierConcreteRealizationClosed = true

periodicCarrierReusesLiteralR290Pair : Bool
periodicCarrierReusesLiteralR290Pair = true

periodicCarrierReusesCenteredResolventCorrection : Bool
periodicCarrierReusesCenteredResolventCorrection = true

euclideanLebesgueRealizationClosedHere : Bool
euclideanLebesgueRealizationClosedHere = false

centeredResolventAnalyticPaymentClosedHere : Bool
centeredResolventAnalyticPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

periodicSignedCarrierConcreteRealizationClosedIsTrue :
  periodicSignedCarrierConcreteRealizationClosed ≡ true
periodicSignedCarrierConcreteRealizationClosedIsTrue = refl

periodicCarrierReusesLiteralR290PairIsTrue :
  periodicCarrierReusesLiteralR290Pair ≡ true
periodicCarrierReusesLiteralR290PairIsTrue = refl

periodicCarrierReusesCenteredResolventCorrectionIsTrue :
  periodicCarrierReusesCenteredResolventCorrection ≡ true
periodicCarrierReusesCenteredResolventCorrectionIsTrue = refl

euclideanLebesgueRealizationClosedHereIsFalse :
  euclideanLebesgueRealizationClosedHere ≡ false
euclideanLebesgueRealizationClosedHereIsFalse = refl

centeredResolventAnalyticPaymentClosedHereIsFalse :
  centeredResolventAnalyticPaymentClosedHere ≡ false
centeredResolventAnalyticPaymentClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
