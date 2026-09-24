{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650C1R406DiagonalCouplingRound652Exact where

------------------------------------------------------------------------
-- ROUND652 / EXACT LIVE COUPLING BETWEEN C1 AND LITERAL R406
--
-- R556 proves on the live R406 slice
--
--   2 * R406
--     = (factoredFull - selfGram) - selfFluxTangent.
--
-- R570 proves on that SAME slice
--
--   factoredFull = 4 * GlobalForcingFull.
--
-- Therefore
--
--   4 * GlobalForcingFull
--     = 2 * R406 + selfGram + selfFluxTangent.
--
-- This is analytically useful because C1 and C2 now visibly share the same
-- literal R406 currency.  The remaining diagonal terms are exactly the
-- self-Gram / self-flux-tangent objects already treated by the temporal
-- diagonal lane.
--
-- No inequality, sign, FTC, endpoint estimate, or Clay promotion is introduced
-- by the pointwise identity.  The integrated identity below uses only the
-- existing integration congruence/additivity authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact as R556
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorBudgetBidiRound570Exact as R570

F : C3.RealField _
F = Rational.rationalRealField

module Coupling
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Reduced = R556.LiveReduced
    Time initialTime integrateTo DerivativeOf
  module Live = R557.LiveIntegrated
    Time initialTime integrateTo DerivativeOf integration
  module Comm = R568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integration
  module Bidi = R570.Bidi
    Time initialTime integrateTo DerivativeOf integration

  fourForcingIsTwoR406PlusDiagonal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    R567.four567 * Comm.globalForcingFull T R cutoff time
    ≡
    R539.two * Flux.At.weightedRemainder T R cutoff time
      + Reduced.At.liveSelfGram T R cutoff time
      + Reduced.At.liveSelfFluxTangent T R cutoff time
  fourForcingIsTwoR406PlusDiagonal T R cutoff time =
    let
      normal =
        Reduced.At.twoLiteralR406RemainderIsReducedNormalForm
          T R cutoff time

      factoredToFour =
        Bidi.liveFactoredIsFourGlobalForcing T R cutoff time

      rearranged :
        Reduced.At.liveFactoredFull T R cutoff time
        ≡
        R539.two * Flux.At.weightedRemainder T R cutoff time
          + Reduced.At.liveSelfGram T R cutoff time
          + Reduced.At.liveSelfFluxTangent T R cutoff time
      rearranged =
        trans
          (sym
            (solve
              ( Reduced.At.liveFactoredFull T R cutoff time
              ∷ Reduced.At.liveSelfGram T R cutoff time
              ∷ Reduced.At.liveSelfFluxTangent T R cutoff time
              ∷ [] )))
          (cong
            (λ value →
              value
                + Reduced.At.liveSelfGram T R cutoff time
                + Reduced.At.liveSelfFluxTangent T R cutoff time)
            normal)
    in
    trans (sym factoredToFour) rearranged

  integratedFourForcingIsTwoR406PlusDiagonal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    R567.four567 * Comm.integratedGlobalForcingFull T R cutoff terminal
    ≡
    R539.two * integrateTo (Live.literalRemainder T R cutoff) terminal
      + integrateTo (Live.selfGram T R cutoff) terminal
      + integrateTo (Live.selfFluxTangent T R cutoff) terminal
  integratedFourForcingIsTwoR406PlusDiagonal
      T R cutoff terminal =
    let
      pointwise :
        (time : Time) →
        R567.four567 * Comm.globalForcingFull T R cutoff time
        ≡
        R539.two * Live.literalRemainder T R cutoff time
          + Live.selfGram T R cutoff time
          + Live.selfFluxTangent T R cutoff time
      pointwise = fourForcingIsTwoR406PlusDiagonal T R cutoff

      integralPointwise :
        integrateTo
          (λ time →
            R567.four567 * Comm.globalForcingFull T R cutoff time)
          terminal
        ≡
        integrateTo
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time
              + Live.selfFluxTangent T R cutoff time)
          terminal
      integralPointwise =
        R495.integrateCongruent integration
          (λ time →
            R567.four567 * Comm.globalForcingFull T R cutoff time)
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time
              + Live.selfFluxTangent T R cutoff time)
          pointwise terminal

      leftScale :
        integrateTo
          (λ time →
            R567.four567 * Comm.globalForcingFull T R cutoff time)
          terminal
        ≡ R567.four567 * Comm.integratedGlobalForcingFull T R cutoff terminal
      leftScale =
        Bidi.integrateFour567
          (Comm.globalForcingFull T R cutoff) terminal

      twoRemainder :
        integrateTo
          (λ time → R539.two * Live.literalRemainder T R cutoff time)
          terminal
        ≡ R539.two * integrateTo (Live.literalRemainder T R cutoff) terminal
      twoRemainder =
        trans
          (R495.integrateCongruent integration
            (λ time → R539.two * Live.literalRemainder T R cutoff time)
            (λ time →
              Live.literalRemainder T R cutoff time
              + Live.literalRemainder T R cutoff time)
            (λ time → solve (Live.literalRemainder T R cutoff time ∷ []))
            terminal)
          (R495.integrateAdd integration
            (Live.literalRemainder T R cutoff)
            (Live.literalRemainder T R cutoff)
            terminal)

      firstAdd :
        integrateTo
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time)
          terminal
        ≡
        integrateTo
          (λ time → R539.two * Live.literalRemainder T R cutoff time)
          terminal
          + integrateTo (Live.selfGram T R cutoff) terminal
      firstAdd =
        R495.integrateAdd integration
          (λ time → R539.two * Live.literalRemainder T R cutoff time)
          (Live.selfGram T R cutoff)
          terminal

      secondAdd :
        integrateTo
          (λ time →
            (R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time)
              + Live.selfFluxTangent T R cutoff time)
          terminal
        ≡
        integrateTo
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time)
          terminal
          + integrateTo (Live.selfFluxTangent T R cutoff) terminal
      secondAdd =
        R495.integrateAdd integration
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time)
          (Live.selfFluxTangent T R cutoff)
          terminal

      rightSplit :
        integrateTo
          (λ time →
            R539.two * Live.literalRemainder T R cutoff time
              + Live.selfGram T R cutoff time
              + Live.selfFluxTangent T R cutoff time)
          terminal
        ≡
        R539.two * integrateTo (Live.literalRemainder T R cutoff) terminal
          + integrateTo (Live.selfGram T R cutoff) terminal
          + integrateTo (Live.selfFluxTangent T R cutoff) terminal
      rightSplit =
        trans secondAdd
          (trans
            (cong
              (_+ integrateTo (Live.selfFluxTangent T R cutoff) terminal)
              firstAdd)
            (trans
              (cong
                (λ value →
                  value
                    + integrateTo (Live.selfGram T R cutoff) terminal
                    + integrateTo (Live.selfFluxTangent T R cutoff) terminal)
                twoRemainder)
              refl))
    in
    trans
      (sym leftScale)
      (trans integralPointwise rightSplit)

------------------------------------------------------------------------
-- Status / analytic interpretation.
------------------------------------------------------------------------

round652PointwiseC1R406DiagonalCouplingClosed : Bool
round652PointwiseC1R406DiagonalCouplingClosed = true

round652IntegratedC1R406DiagonalCouplingClosed : Bool
round652IntegratedC1R406DiagonalCouplingClosed = true

round652C1AndC2ShareLiteralR406Currency : Bool
round652C1AndC2ShareLiteralR406Currency = true

round652DiagonalTermsRemainSameExistingSelfGramFluxObjects : Bool
round652DiagonalTermsRemainSameExistingSelfGramFluxObjects = true

round652IntroducesNewNSEstimate : Bool
round652IntroducesNewNSEstimate = false

round652C1Closed : Bool
round652C1Closed = false

round652C2Closed : Bool
round652C2Closed = false

round652ClayPromotion : Bool
round652ClayPromotion = false

round652PointwiseC1R406DiagonalCouplingClosedIsTrue :
  round652PointwiseC1R406DiagonalCouplingClosed ≡ true
round652PointwiseC1R406DiagonalCouplingClosedIsTrue = refl

round652IntegratedC1R406DiagonalCouplingClosedIsTrue :
  round652IntegratedC1R406DiagonalCouplingClosed ≡ true
round652IntegratedC1R406DiagonalCouplingClosedIsTrue = refl

round652C1AndC2ShareLiteralR406CurrencyIsTrue :
  round652C1AndC2ShareLiteralR406Currency ≡ true
round652C1AndC2ShareLiteralR406CurrencyIsTrue = refl

round652IntroducesNewNSEstimateIsFalse :
  round652IntroducesNewNSEstimate ≡ false
round652IntroducesNewNSEstimateIsFalse = refl

round652C1ClosedIsFalse : round652C1Closed ≡ false
round652C1ClosedIsFalse = refl

round652C2ClosedIsFalse : round652C2Closed ≡ false
round652C2ClosedIsFalse = refl

round652ClayPromotionIsFalse :
  round652ClayPromotion ≡ false
round652ClayPromotionIsFalse = refl
