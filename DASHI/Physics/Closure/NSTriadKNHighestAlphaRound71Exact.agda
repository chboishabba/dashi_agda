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
-- requirement. Round71 proves that per-event decay alone is not decisive: a
-- dyadic branching block doubles multiplicity while halving each floor and
-- preserves total guaranteed floor. Weighted branching has total floor W at
-- every depth; W=E+1 rejects every funding ledger below budget E. Physical
-- descendants must still be genuinely distinct/duplicate-free.
--
-- TRAJECTORY SIDE
--
-- The old unrestricted Q Assignment is formally rejected as the finite cutoff
-- phase space. Round71 constructs six Carrier F slots per canonical reality-
-- orbit representative, exact physical coefficient encoding, and exact ordered
-- alignment of the actual canonical RHS output to those slots.
--
-- One autonomous full-space reality vector field F_N is constructed with fixed
-- N/E/inverse-square/viscosity. Negative modes are reconstructed by conjugation
-- and the nonlinear term is literally the Leray-projected finite Galerkin
-- nonlinearity. Exact positive/negative lookup proves reality is built into the
-- finite carrier. A literal expression evaluator proves degree <=2 at every
-- output mode, and the transverse/divergence-free subspace is invariant under
-- F_N. The remaining pre-trajectory seam is standard actual-real local-
-- Lipschitz/Picard plus global energy continuation.
--
-- CONCENTRATION SIDE
--
-- Round71 applies the repository's exact finite squared Cauchy-Schwarz theorem
-- directly to the triadic physicalAtom values in the ONE Round62 structured PDE
-- list. If the amplification remainder R is exactly their signed sum and
-- 0<=mu<=R, then
--
--       mu^2 <= triadicCount * triadicConcentrationMass.
--
-- This is a non-Carleman amplification-to-mass bridge.  But the cardinality
-- factor is essential: the exact dyadic branching model has signed sum 1 at
-- every depth while squared mass is 2^(-j).  Thus an order-one remainder may be
-- diluted across exponentially many atoms.  The physical concentration theorem
-- must therefore identify a controlled-cardinality/coherent subfibre (or exploit
-- additional sign/geometry) before the squared mass becomes a useful charge.
--
-- QUANTITATIVE DISCRIMINATOR
--
-- A viable propagation generation j needs genuinely distinct physical
-- descendants D_j with floors mu_(j,a) whose accumulated physical charge
--
--       sum_j sum_(a in D_j) mu_(j,a)
--
-- outruns the one finite budget. Uniform floors, slow loss, or fast genuine
-- branching can work; summable TOTAL generation mass remains fatal.
--
-- NEW SHORTEST FRONTIER
--
-- A1. RealPolynomialLocalLipschitzAndPicard: actual-real finite-dimensional
--     local-Lipschitz/Picard for the constructed degree-two field;
-- A2. SelectedGalerkinTrajectoryGlobalEnergyContinuation;
-- B.  LocalizedTrajectoryEmitsStructuredPDEAtoms and identify exactly which
--     projected atom grouping is the critical amplification remainder;
-- C1. CriticalAmplificationForcesControlledSubfibre: prove excess amplification
--     forces a triadic/coherent subfibre with quantitatively controlled
--     cardinality/sign geometry;
-- C2. StructuredSubfibreHasPositiveCharge: consume the constructed Cauchy
--     inequality to obtain the physical concentration floor;
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
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact as Reality
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact as Degree
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalTransverseInvariantRound71Exact as Transverse
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as Cauchy
import DASHI.Physics.Closure.NSTriadKNCriticalCauchyCardinalityDilutionNoGoRound71Exact as Dilution

round71BranchingCompensatesDyadicLossConstructed : Bool
round71BranchingCompensatesDyadicLossConstructed =
  Branching.round71BranchingCompensatesDyadicPerEventLoss

round71FiniteRealCanonicalCarrierConstructed : Bool
round71FiniteRealCanonicalCarrierConstructed =
  FiniteReal.round71FiniteRealCanonicalCoordinateCarrierConstructed

round71CanonicalRHSOutputOnFiniteRealCarrierConstructed : Bool
round71CanonicalRHSOutputOnFiniteRealCarrierConstructed =
  RHSAlignment.round71CanonicalRHSOutputOnFiniteRealCarrier

round71FullSpaceRealityVectorFieldConstructed : Bool
round71FullSpaceRealityVectorFieldConstructed =
  Fixed.round71FullSpaceRealityVectorFieldConstructed

round71RealityBuiltIntoFiniteState : Bool
round71RealityBuiltIntoFiniteState = Reality.round71RealityBuiltIntoFiniteState

round71FixedCanonicalVectorFieldDegreeAtMostTwo : Bool
round71FixedCanonicalVectorFieldDegreeAtMostTwo =
  Degree.round71FixedCanonicalVectorFieldDegreeAtMostTwo

round71TransverseSubspaceInvariant : Bool
round71TransverseSubspaceInvariant =
  Transverse.round71FixedCanonicalTransverseSubspaceInvariant

round71FiniteCauchyRemainderToTriadicMassConstructed : Bool
round71FiniteCauchyRemainderToTriadicMassConstructed =
  Cauchy.round71FiniteCauchyRemainderToTriadicMassConstructed

round71CardinalityDilutionNoGoConstructed : Bool
round71CardinalityDilutionNoGoConstructed =
  Dilution.round71OrderOneRemainderCanHaveDyadicallySmallSquaredMass

-- Genuine remaining physical/analytic producers on the decisive path.
round71RealPolynomialLocalLipschitzAndPicardConstructed : Bool
round71RealPolynomialLocalLipschitzAndPicardConstructed = false

round71SelectedGalerkinTrajectoryConstructed : Bool
round71SelectedGalerkinTrajectoryConstructed = false

round71LiteralTrajectoryEmitsStructuredAtoms : Bool
round71LiteralTrajectoryEmitsStructuredAtoms = false

round71CriticalAmplificationForcesControlledSubfibre : Bool
round71CriticalAmplificationForcesControlledSubfibre = false

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

round71RealityBuiltIntoFiniteStateIsTrue :
  round71RealityBuiltIntoFiniteState ≡ true
round71RealityBuiltIntoFiniteStateIsTrue = refl

round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue :
  round71FixedCanonicalVectorFieldDegreeAtMostTwo ≡ true
round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue = refl

round71TransverseSubspaceInvariantIsTrue :
  round71TransverseSubspaceInvariant ≡ true
round71TransverseSubspaceInvariantIsTrue = refl

round71FiniteCauchyRemainderToTriadicMassConstructedIsTrue :
  round71FiniteCauchyRemainderToTriadicMassConstructed ≡ true
round71FiniteCauchyRemainderToTriadicMassConstructedIsTrue = refl

round71CardinalityDilutionNoGoConstructedIsTrue :
  round71CardinalityDilutionNoGoConstructed ≡ true
round71CardinalityDilutionNoGoConstructedIsTrue = refl

round71RealPolynomialLocalLipschitzAndPicardConstructedIsFalse :
  round71RealPolynomialLocalLipschitzAndPicardConstructed ≡ false
round71RealPolynomialLocalLipschitzAndPicardConstructedIsFalse = refl

round71SelectedGalerkinTrajectoryConstructedIsFalse :
  round71SelectedGalerkinTrajectoryConstructed ≡ false
round71SelectedGalerkinTrajectoryConstructedIsFalse = refl

round71CriticalAmplificationForcesControlledSubfibreIsFalse :
  round71CriticalAmplificationForcesControlledSubfibre ≡ false
round71CriticalAmplificationForcesControlledSubfibreIsFalse = refl

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
