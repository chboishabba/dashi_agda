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
-- One autonomous full-space reality vector field F_N is now constructed with
-- fixed N/E/inverse-square/viscosity and arbitrary Complex3 F values on positive
-- canonical modes. Negative values are reconstructed by conjugation and the
-- nonlinear term is literally the repository's Leray-projected finite Galerkin
-- nonlinearity.
--
-- The following are now theorem-level, not status intentions:
-- * exact positive and negative reality lookup;
-- * reality built into the finite carrier;
-- * an expression evaluator definitionally tied to rawCanonicalRHSAt with
--   algebraic degree <=2 at every output mode;
-- * invariance of the transverse/divergence-free subspace under F_N.
--
-- Consequently the remaining pre-trajectory seam is standard real analysis:
-- flatten the exact degree-two field to the six-real coordinate carrier, prove
-- local Lipschitz for the actual real-number implementation, and invoke finite-
-- dimensional Picard. The NS-specific carrier, polynomial-shape, reality and
-- transversality issues exposed by earlier rounds are no longer open.
--
-- QUANTITATIVE DISCRIMINATOR
--
-- A viable propagation generation j needs genuine physical descendants D_j
-- with floors mu_(j,a) whose distinct accumulated charge
--
--       sum_j sum_(a in D_j) mu_(j,a)
--
-- outruns the one finite physical budget. Uniform floors, slow loss, or fast
-- genuine branching can work; summable TOTAL generation mass remains fatal.
--
-- NEW SHORTEST FRONTIER
--
-- A1. RealPolynomialLocalLipschitzAndPicard: apply actual-real finite-dimensional
--     local-Lipschitz/Picard authority to the constructed degree-two field;
-- A2. SelectedGalerkinTrajectoryGlobalEnergyContinuation: transport the local
--     trajectory through the exact reality/transverse invariants and finite
--     energy identity to obtain the global selected trajectory;
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
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact as Reality
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact as Degree
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalTransverseInvariantRound71Exact as Transverse

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

round71RealityBuiltIntoFiniteState : Bool
round71RealityBuiltIntoFiniteState = Reality.round71RealityBuiltIntoFiniteState

round71FixedCanonicalVectorFieldDegreeAtMostTwo : Bool
round71FixedCanonicalVectorFieldDegreeAtMostTwo =
  Degree.round71FixedCanonicalVectorFieldDegreeAtMostTwo

round71TransverseSubspaceInvariant : Bool
round71TransverseSubspaceInvariant =
  Transverse.round71FixedCanonicalTransverseSubspaceInvariant

-- Genuine remaining physical/analytic producers on the decisive path.
round71RealPolynomialLocalLipschitzAndPicardConstructed : Bool
round71RealPolynomialLocalLipschitzAndPicardConstructed = false

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

round71RealityBuiltIntoFiniteStateIsTrue :
  round71RealityBuiltIntoFiniteState ≡ true
round71RealityBuiltIntoFiniteStateIsTrue = refl

round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue :
  round71FixedCanonicalVectorFieldDegreeAtMostTwo ≡ true
round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue = refl

round71TransverseSubspaceInvariantIsTrue :
  round71TransverseSubspaceInvariant ≡ true
round71TransverseSubspaceInvariantIsTrue = refl

round71RealPolynomialLocalLipschitzAndPicardConstructedIsFalse :
  round71RealPolynomialLocalLipschitzAndPicardConstructed ≡ false
round71RealPolynomialLocalLipschitzAndPicardConstructedIsFalse = refl

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
