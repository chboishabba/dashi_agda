module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound72Exact where

------------------------------------------------------------------------
-- ROUND72 HIGHEST-ALPHA CUTSET
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND72 MATHEMATICAL DELTA
--
-- A. RAW CARDINALITY AUDIT
--
-- * On a fixed literal output fibre, resonance p+q=k leaves one free Z^3
--   input.  p and k determine q exactly.  The crude geometric code lies in one
--   cutoff cube with exact cubic cardinality majorant.
-- * LH/HL improve this to the actual LOW-leg shell: at fixed output the low leg
--   determines the high leg and lies in the 2^ell cube.  Its explicit majorant
--   is (3*2^ell)^3.  HH/CC do not receive a fictitious low-leg bound.
-- * Even optimistic O(N^2) and crude O(N^3) effective cardinality are NOT
--   enough for the Round70 funding contradiction: their reciprocal shell floors
--   2^(-2j), 2^(-3j) have every finite prefix explicitly fundable below E=2.
-- * Four-way branching is the exact critical multiplicity for 2^(-2j) loss;
--   eight-way branching is the exact critical multiplicity for 2^(-3j) loss.
--
-- B. EFFECTIVE-COMPLEXITY CAUCHY
--
-- Replace Round71's unit factorisation a_tau=a_tau*1 by a same-object physical
-- factorisation
--
--      a_tau = x_tau y_tau.
--
-- Exact finite Cauchy gives
--
--      (sum a_tau)^2 <= Q W,
--      Q=sum x_tau^2, W=sum y_tau^2.
--
-- The overlay is indexed by the SAME Round62 LocalizedPDEAtom list, so this is
-- not a parallel concentration carrier.  Round69 critical amplification now
-- composes directly to
--
--      mu^2 <= Q W
--
-- without any ambient Xi<=K hypothesis.
--
-- Crucially, scalar a_tau does not determine Q,W: (1,1) and (2,1/2) have the
-- same product but different charge/complexity.  Therefore a useful overlay
-- must be supplied by actual velocity/Gram/energy structure.
--
-- C. STATIC FINE-SOURCE REFINEMENT
--
-- `StaticPhysicalShellPairing` already retains per-incidence `triadValue`.
-- Round72 refines the exact classified output fibre into one Round62
-- `physicalAtom` per triad, plus the differentiated Com atom, before classwise
-- aggregation.  Flattening that fine list to SignedConstituent reconstructs the
-- exact Round25 five-source total.  LH/HL/CC/Com owners are canonical.  HH has
-- one explicit remaining good/bad owner-selection authority; no duplication is
-- permitted.
--
-- NEW DECISIVE PRODUCERS
--
-- The old Round71
--
--   CriticalAmplificationForcesControlledSubfibre
--
-- is superseded by the sharper same-object theorem
--
--   CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization
--
-- which must prove on the selected localized trajectory:
--
--   1. the critical remainder equals the exact structured triadic grouping;
--   2. every triadic scalar has a PHYSICAL factorisation x_tau*y_tau;
--   3. Q=sum x_tau^2 is a genuine charge paid by the physical budget;
--   4. W=sum y_tau^2 has a sufficiently strong scale bound.
--
-- The companion propagation theorem is
--
--   PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss,
--
-- producing genuinely nonduplicate descendants whose total Q-floor outruns
-- every finite budget.  Raw O(N^2)/O(N^3) counting alone is now formally dead.
--
-- SHORTEST FRONTIER AFTER ROUND72
--
-- A1. RealPolynomialLocalLipschitzAndPicard.
-- A2. SelectedGalerkinTrajectoryGlobalEnergyContinuation.
-- B1. TrajectoryInstantiatesDynamicPhysicalShellBalance.
-- B2. PerIncidenceHHGoodBadSelectionOnTrajectory plus literal localization
--     kernel/tail/boundary atoms; static five-source refinement is constructed.
-- C.  CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization.
-- D.  PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss.
-- E.  CriticalRatioBarrierFromPropagationBudget.
-- F.  Then finish the already-isolated Gram/six-three, HH-bad, soft-data,
--     kernel-boundary, C_c^4/fourfold-decay and scalar-gate closures.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadicMultiplicityLossLedgerRound72Exact as Ledger
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as FineTriadic
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsFineFiveSourceAtomsRound72Exact as FineFive

round72Round71TrajectoryCarrierAdvancesRetained : Bool
round72Round71TrajectoryCarrierAdvancesRetained =
  R71.round71FullSpaceRealityVectorFieldConstructed

round72PhysicalMultiplicityLossLedgerConstructed : Bool
round72PhysicalMultiplicityLossLedgerConstructed = true

round72FixedOutputThreeDOFConstructed : Bool
round72FixedOutputThreeDOFConstructed = Ledger.round72FixedOutputThreeDOFConstructed

round72PolynomialFrequencyCountingNoGoConstructed : Bool
round72PolynomialFrequencyCountingNoGoConstructed =
  Ledger.round72PolynomialFrequencyRawCountingFundingNoGoConstructed

round72FactorizedAmplificationConcentrationConstructed : Bool
round72FactorizedAmplificationConcentrationConstructed =
  Ledger.round72AmplificationFactorizedConcentrationConstructed

round72StaticFineTriadicSourceConstructedModuloHHSelection : Bool
round72StaticFineTriadicSourceConstructedModuloHHSelection =
  FineTriadic.round72StaticFineTriadicAtomsConstructedModuloHHSelection

round72StaticFineFiveSourceConstituentListConstructed : Bool
round72StaticFineFiveSourceConstituentListConstructed =
  FineFive.round72StaticFiveSourceRefinesToOneStructuredConstituentList

-- Remaining trajectory/critical physical producers.
round72RealPolynomialLocalLipschitzAndPicard : Bool
round72RealPolynomialLocalLipschitzAndPicard = false

round72SelectedGalerkinTrajectoryGlobalEnergyContinuation : Bool
round72SelectedGalerkinTrajectoryGlobalEnergyContinuation = false

round72TrajectoryInstantiatesDynamicPhysicalShellBalance : Bool
round72TrajectoryInstantiatesDynamicPhysicalShellBalance = false

round72PerIncidenceHHGoodBadSelectionOnTrajectory : Bool
round72PerIncidenceHHGoodBadSelectionOnTrajectory = false

round72TrajectoryEmitsKernelTailBoundaryAtoms : Bool
round72TrajectoryEmitsKernelTailBoundaryAtoms = false

round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization : Bool
round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization =
  Ledger.round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization

round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss : Bool
round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss =
  Ledger.round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss

round72CriticalRatioBarrierConstructed : Bool
round72CriticalRatioBarrierConstructed = false

round72ClayPromotion : Bool
round72ClayPromotion = false

round72PhysicalMultiplicityLossLedgerConstructedIsTrue :
  round72PhysicalMultiplicityLossLedgerConstructed ≡ true
round72PhysicalMultiplicityLossLedgerConstructedIsTrue = refl

round72StaticFineFiveSourceConstituentListConstructedIsTrue :
  round72StaticFineFiveSourceConstituentListConstructed ≡ true
round72StaticFineFiveSourceConstituentListConstructedIsTrue = refl

round72RealPolynomialLocalLipschitzAndPicardIsFalse :
  round72RealPolynomialLocalLipschitzAndPicard ≡ false
round72RealPolynomialLocalLipschitzAndPicardIsFalse = refl

round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorizationIsFalse :
  round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization ≡ false
round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorizationIsFalse = refl

round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLossIsFalse :
  round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss ≡ false
round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLossIsFalse = refl

round72ClayPromotionIsFalse : round72ClayPromotion ≡ false
round72ClayPromotionIsFalse = refl
