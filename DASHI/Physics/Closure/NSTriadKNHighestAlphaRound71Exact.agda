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
-- Their abstract reports quadruple exponential in the endpoint critical Besov
-- norm and double exponential in the auxiliary L^p norm.
--
-- Authors: Jishan Fan; Song Jiang; Gen Nakamura; Yong Zhou.
-- Title: "Logarithmically Improved Regularity Criteria for the Navier-Stokes
-- and MHD Equations".
-- DOI: 10.1007/s00021-010-0039-5.
--
-- ROUND71 RESULT
--
-- PROPAGATION SIDE
--
-- Round70 identified cumulative non-summability as the exact finite-funding
-- requirement.  Round71 proves the per-event loss rate alone is not decisive:
-- a dyadic branching block doubles descendant multiplicity while halving each
-- descendant floor and preserves total guaranteed floor exactly.  Weighted
-- branching has total floor W at every depth, so W=E+1 rejects every funding
-- ledger below budget E.  This remains an arithmetic viability theorem only;
-- physical descendants must still be genuinely distinct/duplicate-free.
--
-- TRAJECTORY SIDE
--
-- The old Round26/30 Assignment = CoordinateVariable -> Q is formally rejected
-- as the finite cutoff Picard space.  CoordinateVariable contains an injective
-- Nat family of Fourier slots and Q is not the physical real field.
--
-- Round71 constructs:
-- * six ordered Carrier F slots per canonical retained reality-orbit mode;
-- * exact physical TransverseModeCoefficient -> finite-real encoding;
-- * exact ordered alignment of the actual canonical physical RHS output with
--   that same finite-real canonical slot carrier;
-- * a FIXED-CUTOFF autonomous full-space reality vector field.  Its state stores
--   arbitrary Complex3 F values on canonical positive representatives, negatives
--   are reconstructed by conjugation, and N/E/inverse-square/viscosity are fixed
--   independently of the evolving state.  Its nonlinear part is literally the
--   repository's Leray-projected finite Galerkin nonlinearity.
--
-- Thus the structural input/output ODE carrier problem is now closed.  The next
-- A-side theorem is ANALYTIC rather than representational: flatten this exact
-- autonomous field to the six-real coordinates, prove the degree-two/local-
-- Lipschitz formula over the actual real-number authority, invoke finite-
-- dimensional Picard, prove the transverse subspace invariant, then continue
-- globally using the exact finite energy estimate.
--
-- QUANTITATIVE DISCRIMINATOR
--
-- A viable propagation generation j needs genuine physical descendants D_j,
-- with floors mu_(j,a), such that
--
--       sum_j sum_(a in D_j) mu_(j,a)
--
-- outruns the one finite physical budget.  Uniform floors, sufficiently slow
-- loss, or sufficiently fast genuine branching can work.  Summable TOTAL
-- generation mass remains fatal.  Log-improved criteria are architectural
-- precedent only; they are not imported as an unconditional C1 producer.
--
-- NEW SHORTEST FRONTIER
--
-- A1. FiniteRealCanonicalVectorFieldPolynomialLipschitz: prove the exact fixed
--     full-space reality field is a degree-two locally-Lipschitz real vector
--     field in the constructed six-real coordinates;
-- A2. SelectedGalerkinTrajectoryExistsAndStaysPhysical: finite-dimensional real
--     Picard, transverse invariance, and global energy continuation;
-- B.  LocalizedTrajectoryEmitsStructuredPDEAtoms;
-- C.  CriticalAmplificationForcesStructuredConcentration;
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
import DASHI.Physics.Closure.NSTriadKNCanonicalRHSFiniteRealSlotAlignmentRound71Exact as RHSAlignment
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed

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

round71CanonicalRHSOutputOnFiniteRealCarrierConstructed : Bool
round71CanonicalRHSOutputOnFiniteRealCarrierConstructed =
  RHSAlignment.round71CanonicalRHSOutputOnFiniteRealCarrier

round71FixedCanonicalGeometryIndependentOfState : Bool
round71FixedCanonicalGeometryIndependentOfState =
  Fixed.round71FixedCanonicalGeometryIndependentOfState

round71FullSpaceRealityVectorFieldConstructed : Bool
round71FullSpaceRealityVectorFieldConstructed =
  Fixed.round71FullSpaceRealityVectorFieldConstructed

-- Genuine remaining physical/analytic producers on the decisive path.
round71FiniteRealCanonicalVectorFieldPolynomialLipschitz : Bool
round71FiniteRealCanonicalVectorFieldPolynomialLipschitz =
  Fixed.round71FullSpaceRealCoordinatePolynomialLipschitzConstructed

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

round71CanonicalRHSOutputOnFiniteRealCarrierConstructedIsTrue :
  round71CanonicalRHSOutputOnFiniteRealCarrierConstructed ≡ true
round71CanonicalRHSOutputOnFiniteRealCarrierConstructedIsTrue = refl

round71FixedCanonicalGeometryIndependentOfStateIsTrue :
  round71FixedCanonicalGeometryIndependentOfState ≡ true
round71FixedCanonicalGeometryIndependentOfStateIsTrue = refl

round71FullSpaceRealityVectorFieldConstructedIsTrue :
  round71FullSpaceRealityVectorFieldConstructed ≡ true
round71FullSpaceRealityVectorFieldConstructedIsTrue = refl

round71FiniteRealCanonicalVectorFieldPolynomialLipschitzIsFalse :
  round71FiniteRealCanonicalVectorFieldPolynomialLipschitz ≡ false
round71FiniteRealCanonicalVectorFieldPolynomialLipschitzIsFalse = refl

round71SelectedGalerkinTrajectoryConstructedIsFalse :
  round71SelectedGalerkinTrajectoryConstructed ≡ false
round71SelectedGalerkinTrajectoryConstructedIsFalse = refl

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
