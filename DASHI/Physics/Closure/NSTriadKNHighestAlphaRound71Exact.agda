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
-- Round71 now shows that the PER-EVENT loss rate is not by itself decisive:
-- genuine multiplicity can compensate loss.
--
-- PROPAGATION-SIDE CONSTRUCTIONS
--
-- 1. A literal finite dyadic branching block.  Depth zero contains one unit
--    floor.  Each step duplicates the block and halves all descendant floors.
--    The recursive event count doubles exactly.
--
-- 2. Exact mass conservation:
--
--        totalFloor(depth) = 1.
--
--    Thus doubling multiplicity exactly compensates factor-1/2 descendant loss.
--
-- 3. Weighted version:
--
--        totalFloor(weightedBlock W depth) = W.
--
--    Taking W=E+1 rejects every Round70 funding ledger below budget E at every
--    finite depth.  Therefore exponential pointwise loss is not automatically
--    fatal if physical descendant multiplicity grows fast enough.
--
-- This remains arithmetic/combinatorial only.  Round70 already proves abstract
-- block indices do not imply physical support separation; formal duplicates may
-- not be charged twice.  The hard physical theorem is multiplicity x loss on
-- genuinely distinct frequency/spacetime descendants.
--
-- TRAJECTORY-SIDE AUDIT AND REPAIR
--
-- 4. The old Round26/30 Picard `Assignment = CoordinateVariable -> Q` is NOT
--    the finite cutoff carrier.  CoordinateVariable contains an injective copy
--    of Nat via modes (n,0,0), so a finite equation list does not make the
--    unrestricted function assignment finite-dimensional.  It is also Q-valued
--    whereas the physical Complex3 carrier uses Carrier F.
--
-- 5. Round71 constructs the replacement finite REAL carrier: exactly six
--    ordered scalar slots (x.re,x.im,y.re,y.im,z.re,z.im) for every canonical
--    retained reality-orbit mode, with values in the SAME Carrier F as the
--    physical Fourier coefficients.  The slot count is exactly six times the
--    canonical mode-list count.
--
-- 6. Every literal TransverseModeCoefficient is encoded into those six real
--    slots, and finite folding preserves the exact coefficient-mode slot order.
--    Thus the physical -> finite-real encoding half of the trajectory bridge is
--    constructed without rationalizing physical data.
--
-- The reverse map is deliberately fail-closed: arbitrary six-tuples need not be
-- transverse.  The remaining trajectory producer must either (i) construct a
-- genuine transverse four-real-coordinate chart, or (ii) extend the projected
-- RHS to the full finite six-component real space, prove local Lipschitz there,
-- and prove the transverse subspace is invariant.
--
-- QUANTITATIVE DISCRIMINATOR
--
-- A viable propagation generation j needs genuine physical descendants D_j,
-- with floors mu_(j,a), such that
--
--       sum_j sum_(a in D_j) mu_(j,a)
--
-- outruns the one finite physical budget.  Uniform floors, sufficiently slow
-- losses, or sufficiently fast genuine branching can all work.  Summable TOTAL
-- generation mass remains fatal.  The logarithmically improved regularity
-- literature is only architectural precedent for accumulated/divergence
-- criteria; it is not imported as an unconditional C1 producer.
--
-- NEW SHORTEST FRONTIER
--
-- A1. CanonicalPhysicalRHSActsOnFiniteRealCarrier: finish the same-object
--     finite REAL vector-field chart and local-Lipschitz representation;
-- A2. SelectedGalerkinTrajectoryExistsAndStaysPhysical: real Picard trajectory,
--     transverse/reality/cutoff invariance, and energy continuation;
-- B.  LocalizedTrajectoryEmitsStructuredPDEAtoms;
-- C.  CriticalAmplificationForcesStructuredConcentration, with an explicit
--     initial physical charge floor and no Xi<=K premise;
-- D1. PhysicalPropagationProducesDuplicateFreeDescendants;
-- D2. PhysicalMultiplicityLossBalanceOutrunsBudget;
-- E.  CriticalRatioBarrierFromPropagationFloors;
-- F.  only after A-E survive, finish Gram/HH-bad/data/kernel/continuum/gate.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound70Exact
import DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact as Branching
import DASHI.Physics.Closure.NSTriadKNOldRationalAssignmentNotFiniteCutoffRound71Exact as OldNoGo
import DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact as FiniteReal
import DASHI.Physics.Closure.NSTriadKNPhysicalCoefficientFiniteRealEncodingRound71Exact as Encoding

round71BranchingCompensatesDyadicLossConstructed : Bool
round71BranchingCompensatesDyadicLossConstructed =
  Branching.round71BranchingCompensatesDyadicPerEventLoss

round71MultiplicityMustBePhysicalAndDuplicateFree : Bool
round71MultiplicityMustBePhysicalAndDuplicateFree =
  Branching.round71MultiplicityMustBePhysicalAndDuplicateFree

round71OldAssignmentNatInjectionConstructed : Bool
round71OldAssignmentNatInjectionConstructed =
  OldNoGo.round71OldAssignmentDomainContainsNatInjection

round71FiniteRealCanonicalCarrierConstructed : Bool
round71FiniteRealCanonicalCarrierConstructed =
  FiniteReal.round71FiniteRealCanonicalCoordinateCarrierConstructed

round71PhysicalToFiniteRealEncodingConstructed : Bool
round71PhysicalToFiniteRealEncodingConstructed =
  Encoding.round71PhysicalCoefficientFiniteRealEncodingConstructed

-- Genuine remaining physical producers on the decisive path.
round71CanonicalPhysicalRHSActsOnFiniteRealCarrier : Bool
round71CanonicalPhysicalRHSActsOnFiniteRealCarrier = false

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

round71OldAssignmentNatInjectionConstructedIsTrue :
  round71OldAssignmentNatInjectionConstructed ≡ true
round71OldAssignmentNatInjectionConstructedIsTrue = refl

round71FiniteRealCanonicalCarrierConstructedIsTrue :
  round71FiniteRealCanonicalCarrierConstructed ≡ true
round71FiniteRealCanonicalCarrierConstructedIsTrue = refl

round71PhysicalToFiniteRealEncodingConstructedIsTrue :
  round71PhysicalToFiniteRealEncodingConstructed ≡ true
round71PhysicalToFiniteRealEncodingConstructedIsTrue = refl

round71CanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse :
  round71CanonicalPhysicalRHSActsOnFiniteRealCarrier ≡ false
round71CanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse = refl

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
