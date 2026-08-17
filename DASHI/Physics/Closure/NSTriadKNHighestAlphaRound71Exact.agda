module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound71Exact where

------------------------------------------------------------------------
-- ROUND 71 HIGHEST-ALPHA CUTSET
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
-- Quantitative dependence: triple exponential in the critical L^3 bound.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Ruilin Hu; Phuoc-Tai Nguyen; Quoc-Hung Nguyen; Ping Zhang.
-- Title: "Quantitative bounds for bounded solutions to the Navier-Stokes
-- equations in endpoint critical Besov spaces".
-- arXiv DOI: 10.48550/arXiv.2411.06483.
-- Quantitative dependence reported in the abstract: quadruple exponential in
-- the endpoint critical Besov norm and double exponential in the auxiliary
-- L^p norm.  This corrects the earlier informal "triple exponential" gloss.
--
-- Authors: Jishan Fan; Song Jiang; Gen Nakamura; Yong Zhou.
-- Title: "Logarithmically Improved Regularity Criteria for the Navier-Stokes
-- and MHD Equations".
-- DOI: 10.1007/s00021-010-0039-5.
--
-- ROUND71 RESULT
--
-- Round70 identified cumulative non-summability as the exact finite-funding
-- requirement and falsified one-event-per-depth dyadic floors 1,1/2,1/4,... .
-- Round71 now shows that the PER-EVENT loss rate is not by itself decisive.
-- Multiplicity can compensate loss.
--
-- CONSTRUCTED:
--
-- 1. A literal finite dyadic branching block.  Depth zero contains one unit
--    floor.  Each propagation step duplicates the entire block and halves all
--    descendant floors.  The recursive event count doubles exactly.
--
-- 2. Exact mass conservation under that branching law:
--
--        totalFloor(depth) = 1
--
--    for every finite depth.  Thus doubling multiplicity exactly compensates
--    a factor-1/2 loss per descendant.
--
-- 3. Weighted version.  For every rational W,
--
--        totalFloor(weightedBlock W depth) = W.
--
--    Hence for every finite budget E, choosing W=E+1 gives a finite floor block
--    with cumulative requirement E+1>E at EVERY depth.  Round70 funding then
--    rejects every possible event ledger fitting under budget E.
--
-- This is intentionally only an arithmetic / combinatorial viability theorem.
-- It does NOT claim that Navier-Stokes supplies 2^j distinct descendants.
-- Round70 already showed that abstract block indices do not imply physical
-- support separation, so formal duplication cannot be charged twice.
--
-- QUANTITATIVE DISCRIMINATOR
--
-- The physical propagation question is therefore not merely
--
--       how fast does one event's charge floor decay?
--
-- but
--
--       how does genuine duplicate-free descendant multiplicity
--       compare with the per-descendant propagation loss?
--
-- Symbolically, a viable generation j needs enough actual physical descendants
-- D_j, with individual floors mu_(j,a), that the accumulated distinct charge
--
--       sum_j sum_(a in D_j) mu_(j,a)
--
-- outruns the one finite energy/enstrophy budget.  A uniform floor is one route;
-- slow/logarithmic loss is another; sufficiently fast genuine branching is a
-- third.  Summable TOTAL generation mass remains fatal to the finite-funding
-- route regardless of event count.
--
-- The logarithmically improved regularity literature is recorded only as
-- architectural precedent for accumulated/divergence criteria.  It is not
-- imported as a producer of the missing unconditional C1 bound.
--
-- NEW SHORTEST FRONTIER:
--
-- A. SelectedGalerkinTrajectoryExistsAndStaysPhysical;
-- B. LocalizedTrajectoryEmitsStructuredPDEAtoms;
-- C. CriticalAmplificationForcesStructuredConcentration, with an explicit
--    initial physical charge floor and no Xi<=K premise;
-- D1. PhysicalPropagationProducesDuplicateFreeDescendants: construct the
--     actual frequency/spacetime descendants on that SAME trajectory and prove
--     they are charge-distinct rather than formal duplicates;
-- D2. PhysicalMultiplicityLossBalanceOutrunsBudget: prove the sum of the
--     descendant floors, including propagation losses and multiplicities,
--     eventually exceeds the finite physical budget;
-- E. CriticalRatioBarrierFromPropagationFloors;
-- F. only after A-E survive, finish the existing Gram/HH-bad/data/kernel/
--    continuum/final-gate closures.
--
-- Counting D1+D2 separately, the decisive critical package is now six named
-- physical lemmas rather than five; the increase is a clarification of the one
-- previously bundled propagation lemma, not a new downstream package.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound70Exact
import DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact as Branching

round71BranchingCompensatesDyadicLossConstructed : Bool
round71BranchingCompensatesDyadicLossConstructed =
  Branching.round71BranchingCompensatesDyadicPerEventLoss

round71MultiplicityMustBePhysicalAndDuplicateFree : Bool
round71MultiplicityMustBePhysicalAndDuplicateFree =
  Branching.round71MultiplicityMustBePhysicalAndDuplicateFree

-- Genuine remaining physical producers on the decisive path.
round71SelectedGalerkinTrajectoryConstructed : Bool
round71SelectedGalerkinTrajectoryConstructed = false

round71LiteralTrajectoryEmitsStructuredAtoms : Bool
round71LiteralTrajectoryEmitsStructuredAtoms = false

round71CriticalAmplificationForcesStructuredConcentration : Bool
round71CriticalAmplificationForcesStructuredConcentration = false

round71PhysicalPropagationProducesDuplicateFreeDescendants : Bool
round71PhysicalPropagationProducesDuplicateFreeDescendants = false

round71PhysicalMultiplicityLossBalanceOutrunsBudget : Bool
round71PhysicalMultiplicityLossBalanceOutrunsBudget = false

round71CriticalRatioBarrierConstructed : Bool
round71CriticalRatioBarrierConstructed = false

round71ClayPromotion : Bool
round71ClayPromotion = false

round71BranchingCompensatesDyadicLossConstructedIsTrue :
  round71BranchingCompensatesDyadicLossConstructed ≡ true
round71BranchingCompensatesDyadicLossConstructedIsTrue = refl

round71MultiplicityMustBePhysicalAndDuplicateFreeIsTrue :
  round71MultiplicityMustBePhysicalAndDuplicateFree ≡ true
round71MultiplicityMustBePhysicalAndDuplicateFreeIsTrue = refl

round71SelectedGalerkinTrajectoryConstructedIsFalse :
  round71SelectedGalerkinTrajectoryConstructed ≡ false
round71SelectedGalerkinTrajectoryConstructedIsFalse = refl

round71LiteralTrajectoryEmitsStructuredAtomsIsFalse :
  round71LiteralTrajectoryEmitsStructuredAtoms ≡ false
round71LiteralTrajectoryEmitsStructuredAtomsIsFalse = refl

round71CriticalAmplificationForcesStructuredConcentrationIsFalse :
  round71CriticalAmplificationForcesStructuredConcentration ≡ false
round71CriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round71PhysicalPropagationProducesDuplicateFreeDescendantsIsFalse :
  round71PhysicalPropagationProducesDuplicateFreeDescendants ≡ false
round71PhysicalPropagationProducesDuplicateFreeDescendantsIsFalse = refl

round71PhysicalMultiplicityLossBalanceOutrunsBudgetIsFalse :
  round71PhysicalMultiplicityLossBalanceOutrunsBudget ≡ false
round71PhysicalMultiplicityLossBalanceOutrunsBudgetIsFalse = refl

round71CriticalRatioBarrierConstructedIsFalse :
  round71CriticalRatioBarrierConstructed ≡ false
round71CriticalRatioBarrierConstructedIsFalse = refl

round71ClayPromotionIsFalse : round71ClayPromotion ≡ false
round71ClayPromotionIsFalse = refl
