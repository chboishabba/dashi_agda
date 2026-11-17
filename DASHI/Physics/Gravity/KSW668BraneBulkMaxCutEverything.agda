module DASHI.Physics.Gravity.KSW668BraneBulkMaxCutEverything where

------------------------------------------------------------------------
-- Authoritative source-only D2 KSW/GRQFT brane/KK rollup.
--
-- Same established DASHI PR #1504; no parallel rollup PR.
-- ORIGINAL SOURCE: Caldwell & Langlois (2001) Phys Lett B 511,
-- 129-135, DOI 10.1016/S0370-2693(01)00631-1,
-- arXiv gr-qc/0103070, Eqs 1,4,17-20.
--
-- Typed original-rational finite subgates live here. Differentiable
-- Lorentzian/AdS tensor and horizon integrals have independent SymPy and
-- mpmath *numerical/symbolic* receipts only. Agda 2.9 has NOT run on
-- these new theorem owners. No source experimental gravity data here.
------------------------------------------------------------------------

import DASHI.Physics.Gravity.KSW668KaluzaKleinSpacelikeFiberCausalExact
import DASHI.Physics.Gravity.KSW668FiveDimensionalEinsteinScalarFRWFriedmannExact
import DASHI.Physics.Gravity.KSW668BraneBulkRationalNullComparatorExact
import DASHI.Physics.Gravity.KSW668BraneWindingSourceFiniteExact
import DASHI.Physics.Gravity.KSW668CaldwellLangloisHorizonSourceRationalExact
import DASHI.Physics.Gravity.KSW668BraneLevinStringTSFVPromotionBoundaryExact
import DASHI.Physics.Gravity.KSW668AdS5IsraelOriginalRationalSliceExact
import DASHI.Physics.Gravity.KSW668BulkScalarReceiverRationalSliceExact

-- New independent rational-only source witnesses; no Agda kernel receipt.
import DASHI.Physics.Gravity.KSW668CylinderZ2WindingIsraelRationalExact
import DASHI.Physics.Gravity.KSW668AdS5LinearIsraelTTRationalSliceExact

-- Original moving Neumann normal condition, plus explicit REUSE of
-- DASHI Balaban finite/weighted Neumann-series algebra. Different uses of
-- 'Neumann' are not conflated; the physical 5D FIO is still OPEN.
import DASHI.Physics.Gravity.KSW668AdS5MovingNeumannCharacteristicRationalExact
import DASHI.Physics.Gravity.KSW668AdS5FrozenNeumannSeriesReuseExact

-- UV/IR cutoff reuse: exact Balaban finite dyadic tail conditional on
-- original physical adjacent-cutoff estimate; no false F8 convergence.
import DASHI.Physics.Gravity.KSW668AdS5UVIRDyadicTailReuseExact

-- New F8: actual original moving bulk/Neumann tensor prepotential
-- commutation and exact three-component TT angular polynomial algebra.
-- Both source-derived continuum analytic hypotheses and the numerical
-- source-to-receiver convergence are guarded as separate OPEN gates.
import DASHI.Physics.Gravity.KSW668AdS5TensorPrepotentialCommutationExact
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact

-- Original a=t TT radial 3/7/11-dim effective multipoles: EXACT
-- rational first-cell conservative finite-volume quadratic identities.
-- General source/observer convergence and pinned Agda kernel remain OPEN.
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact

-- Original moving a=t Neumann TT forced characteristic boundary-flux
-- exact rational square; full continuum/SSPRK3/receiver Weyl gate OPEN.
import DASHI.Physics.Gravity.KSW668AdS5MovingNeumannFluxRationalExact

-- F8 VII: exact finite-grid first-order normal SBP forward/backward
-- rational telescopes. The original second-order normal boundary closure
-- has an exact integer energy-injection counterexample (277/2);
-- SBP2 SAT is an alternative weak-Israel discretization.
-- Continuous / fully discrete normal-only source-energy contracts exist
-- independently; coupled (T,y,r), H^(4+epsilon) Weyl trace, FIO,
-- pinned Agda kernel and physical observation all remain OPEN.
import DASHI.Physics.Gravity.KSW668AdS5MovingNormalFiniteSBPTelescopeExact

-- Exact SSPRK3 pure radial imaginary-axis rational amplification identity
-- for the original effective 3/7/11 radial multipoles. The positive-real
-- spectral CFL, full moving y/r/warp coupling, Agda kernel and Weyl
-- observations remain independent OPEN gates.
import DASHI.Physics.Gravity.KSW668AdS5RadialSSPRK3ImaginaryPolynomialExact

-- XXVIII: exact algebraic relation between ORIGINAL E4 and E5 receiver
-- formulae. This is NOT an AdS5 covariant electric-Weyl identification;
-- G1 metric/gauge/linearized-curvature and higher-trace gates remain OPEN.
import DASHI.Physics.Gravity.KSW668F8DualElectricWeylReadoutAlgebraExact
