module DASHI.Physics.Closure.NSTriadKNClayTopDownConsumerRound90Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Tosio Kato.
-- Title: "Strong Lp-Solutions of the Navier-Stokes Equation in Rm, with
-- Applications to Weak Solutions".
-- DOI: 10.1007/BF01174182.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier-Stokes
-- Equations".
-- DOI: 10.1007/BF02392477.
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- DOI: 10.1007/BF00281418.
--
-- Author: Shin-ichi Inage.
-- Title: "Conditional Regularity of the Three-Dimensional Navier-Stokes
-- Equations via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
--
-- ROUND90 / RESTORE THE TOP-DOWN CLAY CONSUMER
--
-- Rounds62--89 repeatedly decomposed the proof into source-facing estimates.
-- That was useful while the consumer was unclear, but Round89 exposed a cost:
-- a purported leaf (`strong six-three x two viscous derivatives`) disappeared
-- after the Clay-level consumer was opened and the frequency factor p.q was
-- moved inside the gradient tensor before majorization.
--
-- Therefore this file deliberately does NOT prescribe a fixed number of
-- leaves.  It starts at the actual continuation consumer.
--
-- The existing Round29 compactness/Serrin module already proves the numerical
-- critical-to-Serrin estimate
--
--   integral L6^4
--     <= C_S^4 (sup H^(1/2)^2) (integral H^(3/2)^2).
--
-- What the Clay proof must construct is not a detached Bool named H2 followed
-- by another Bool named H3.  It must construct, for the SAME limiting strong
-- solution, a critical barrier whose quantitative budget yields the L4_t L6_x
-- continuation predicate consumed by Serrin.
--
-- `CriticalBarrierFor` is indexed by that literal solution.  Consequently the
-- final theorem below cannot silently switch representatives between
-- Galerkin compactness, the critical observable, and continuation.
--
-- This fuses the old H2/H3 interface at the correct abstraction boundary:
--
--   physical finite-Galerkin / C4 / C5 chain
--       -> CriticalBarrierFor limitingSolution
--       -> Serrin continuation of THAT limitingSolution.
--
-- No global regularity claim is made here because no physical
-- `CriticalBarrierFor` is manufactured by this file.  The point is to make the
-- top consumer exact first and drive all remaining proof search downward from
-- this type rather than from a pre-counted list of leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical

record CriticalBarrierFor
    (continuation : Critical.PeriodicSerrinContinuationTarget)
    (solution : Critical.StrongSolution continuation) : Set where
  constructor critical-barrier-for
  field
    budget : Critical.CriticalToSerrinBudget

    -- This field is the SAME-SOLUTION bridge.  It is stronger than merely
    -- knowing a sequence of Galerkin numbers is bounded: the quantitative
    -- Round29 estimate, on this budget, must witness the precise continuation
    -- predicate for this very solution.
    quantitativeBoundGivesL4L6Finite :
      Critical.integralL6Fourth budget
      ≤ Critical.sobolevConstantFourth budget
          * (Critical.supHOneHalfSquared budget
            * Critical.integralHThreeHalfSquared budget) →
      Critical.L4L6Finite continuation solution

open CriticalBarrierFor public

criticalBarrierProducesSerrinWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget}
    {solution : Critical.StrongSolution continuation} →
  CriticalBarrierFor continuation solution →
  Critical.L4L6Finite continuation solution
criticalBarrierProducesSerrinWitness barrier =
  quantitativeBoundGivesL4L6Finite barrier
    (Critical.criticalToSerrinQuantitative (budget barrier))

topDownCriticalBarrierContinuesSameSolution :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget}
    {solution : Critical.StrongSolution continuation} →
  CriticalBarrierFor continuation solution →
  Critical.ExtendsPastMaximalTime continuation solution
topDownCriticalBarrierContinuesSameSolution {continuation} {solution} barrier =
  Critical.serrinContinuation continuation solution
    (criticalBarrierProducesSerrinWitness barrier)

------------------------------------------------------------------------
-- Top-down physical producer.
--
-- This is intentionally a SINGLE consumer-facing object.  It does not encode
-- how many analytic lemmas are used to build the barrier.  C4 pressure,
-- gradient-tensor HH absorption, advective commutators, residual budgets,
-- occupation/replenishment, Galerkin compactness, and limit lower
-- semicontinuity may fuse or split as the mathematics dictates.  Their only
-- top-level obligation is to construct this same-solution barrier.
------------------------------------------------------------------------

record TopDownClayProducer : Set₁ where
  field
    continuation : Critical.PeriodicSerrinContinuationTarget
    limitingSolution : Critical.StrongSolution continuation
    limitingCriticalBarrier :
      CriticalBarrierFor continuation limitingSolution

open TopDownClayProducer public

topDownProducerExtendsLimitingSolution :
  (producer : TopDownClayProducer) →
  Critical.ExtendsPastMaximalTime
    (continuation producer)
    (limitingSolution producer)
topDownProducerExtendsLimitingSolution producer =
  topDownCriticalBarrierContinuesSameSolution
    (limitingCriticalBarrier producer)

round90TopDownClayConsumerConstructed : Bool
round90TopDownClayConsumerConstructed = true

round90OldH2H3FuseAtSameSolutionBarrierInterface : Bool
round90OldH2H3FuseAtSameSolutionBarrierInterface = true

round90PhysicalTopDownClayProducerConstructed : Bool
round90PhysicalTopDownClayProducerConstructed = false

round90FixedLeafCountIsProofInvariant : Bool
round90FixedLeafCountIsProofInvariant = false

round90ClayPromotion : Bool
round90ClayPromotion = false

round90TopDownClayConsumerConstructedIsTrue :
  round90TopDownClayConsumerConstructed ≡ true
round90TopDownClayConsumerConstructedIsTrue = refl

round90OldH2H3FuseAtSameSolutionBarrierInterfaceIsTrue :
  round90OldH2H3FuseAtSameSolutionBarrierInterface ≡ true
round90OldH2H3FuseAtSameSolutionBarrierInterfaceIsTrue = refl

round90PhysicalTopDownClayProducerConstructedIsFalse :
  round90PhysicalTopDownClayProducerConstructed ≡ false
round90PhysicalTopDownClayProducerConstructedIsFalse = refl

round90FixedLeafCountIsProofInvariantIsFalse :
  round90FixedLeafCountIsProofInvariant ≡ false
round90FixedLeafCountIsProofInvariantIsFalse = refl

round90ClayPromotionIsFalse : round90ClayPromotion ≡ false
round90ClayPromotionIsFalse = refl
