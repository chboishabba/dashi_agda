{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650LiveGlobalCommutatorNestedTriadRound695Exact where

------------------------------------------------------------------------
-- ROUND695 / LIVE R694 SPECIALIZATION ON THE ACTUAL R240/R405 TRAJECTORY
--
-- R228 already carries all-mode transversality, so R694's nested four-helicity
-- expansion needs no new trajectory hypothesis.  At each (N,t), instantiate
-- the physical wrapper and obtain
--
--   NestedGlobal_N(t) = 4 * PairCommutatorGlobal_N(t)
--                     = 4 * CoherentCommutatorGlobal_N(t).
--
-- The selected output list is the same literal nonzero cutoff list used by
-- R690/R691.  No estimate or additional carrier assumption is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694

F : C3.RealField _
F = Rational.rationalRealField

module LiveNested
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat)
      (time : Time) where

    retained = Support.toRetainedSupportRealization T R

    physicalSystem =
      Live.physicalSystemAt T retained cutoff time

    S = Dyn.Base.S (Dyn.forgetDynamics T)
    L = Dyn.Base.L (Dyn.forgetDynamics T)
    H = Dyn.Base.H (Dyn.forgetDynamics T)

    allModeTransverse :
      (mode : _) →
      _
    allModeTransverse mode =
      Dyn.Base.velocityTransverse
        (Dyn.forgetDynamics T) cutoff time mode

    module Nested =
      R694.NestedExpansion
        physicalSystem S L H allModeTransverse

    module Pair =
      R692.Expansion physicalSystem S

    liveNestedNonzeroSum : ℚ
    liveNestedNonzeroSum =
      Nested.sumOutputNestedPairs
        (DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.nonzeroCutoffModes cutoff)

    livePairCommutatorNonzeroSum : ℚ
    livePairCommutatorNonzeroSum =
      Pair.nonzeroGlobalPairIncidenceSum

    liveCoherentCommutatorNonzeroSum : ℚ
    liveCoherentCommutatorNonzeroSum =
      Pair.nonzeroGlobalCommutatorWork

    nestedIsFourPairCommutator :
      liveNestedNonzeroSum
      ≡ R694.four * livePairCommutatorNonzeroSum
    nestedIsFourPairCommutator =
      Nested.globalNestedPairsAreFourCommutatorPairs
        (DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.nonzeroCutoffModes cutoff)

    nestedIsFourCoherentCommutator :
      liveNestedNonzeroSum
      ≡ R694.four * liveCoherentCommutatorNonzeroSum
    nestedIsFourCoherentCommutator =
      trans
        nestedIsFourPairCommutator
        (cong
          (R694.four *_)
          (sym Pair.nonzeroGlobalCommutatorIsLiteralPairIncidenceSum))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round695LiveTrajectorySuppliesAllModeTransversality : Bool
round695LiveTrajectorySuppliesAllModeTransversality = true

round695LiveNonzeroNestedTriadExpansionClosed : Bool
round695LiveNonzeroNestedTriadExpansionClosed = true

round695LiveNestedSumIsFourGlobalCoherentCommutator : Bool
round695LiveNestedSumIsFourGlobalCoherentCommutator = true

round695IntroducesNewTrajectoryHypothesis : Bool
round695IntroducesNewTrajectoryHypothesis = false

round695IntroducesEstimate : Bool
round695IntroducesEstimate = false

round695OrbitResidueCancellationClosed : Bool
round695OrbitResidueCancellationClosed = false

round695ClayPromotion : Bool
round695ClayPromotion = false

round695LiveTrajectorySuppliesAllModeTransversalityIsTrue :
  round695LiveTrajectorySuppliesAllModeTransversality ≡ true
round695LiveTrajectorySuppliesAllModeTransversalityIsTrue = refl

round695LiveNonzeroNestedTriadExpansionClosedIsTrue :
  round695LiveNonzeroNestedTriadExpansionClosed ≡ true
round695LiveNonzeroNestedTriadExpansionClosedIsTrue = refl

round695LiveNestedSumIsFourGlobalCoherentCommutatorIsTrue :
  round695LiveNestedSumIsFourGlobalCoherentCommutator ≡ true
round695LiveNestedSumIsFourGlobalCoherentCommutatorIsTrue = refl

round695IntroducesNewTrajectoryHypothesisIsFalse :
  round695IntroducesNewTrajectoryHypothesis ≡ false
round695IntroducesNewTrajectoryHypothesisIsFalse = refl

round695IntroducesEstimateIsFalse :
  round695IntroducesEstimate ≡ false
round695IntroducesEstimateIsFalse = refl

round695OrbitResidueCancellationClosedIsFalse :
  round695OrbitResidueCancellationClosed ≡ false
round695OrbitResidueCancellationClosedIsFalse = refl

round695ClayPromotionIsFalse :
  round695ClayPromotion ≡ false
round695ClayPromotionIsFalse = refl
