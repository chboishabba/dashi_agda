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

-- F8 VIII: original a=t physical moving AdS5 TT full coupled
-- homogeneous weighted-SBP2/SAT + exact radial FV symmetrizer algebra,
-- forced Neumann boundary term and characteristic source lift.
-- Generic rational polynomial lemmas in Agda SOURCE, not pinned kernel.
-- Actual complete T-y-r semidiscrete Gronwall on original t>=1
-- verified separately; fully discrete RK3, H4+Weyl and FIO still OPEN.
import DASHI.Physics.Gravity.KSW668AdS5OriginalCoupledSBPSymmetrizerRationalExact

-- F8 IX original a=t physical characteristic C=DyU-(P-M)/2.
-- Unweighted normal SBP2 SAT stage preserves C exactly at every
-- interior node (even across all SSPRK3 stages and sourced Israel);
-- weighted split SBP4 has explicit interior D-Dw commutator defect.
-- Weak SAT global boundary constraint has rational t4/3 negative control.
-- The full coupled mode3 weighted energy gets explicit commutator bound
-- E' <= (5+16t)E for dy<=b/4; forced source lift E' <= (6+16t)E+||F||²/2.
-- Actual Agda rational source, pinned kernel NOT run.
import DASHI.Physics.Gravity.KSW668AdS5OriginalTTCharacteristicConstraintRationalExact

-- Finite radial -L_d Sobolev powers commute with all original moving
-- y/warp/SAT operators, with source powers treated in parallel.
-- Generic natural-order Agda induction conditional on single
-- commutator; concrete finite matrices checked independently.
-- NOT a mesh-uniform 5D H4+epsilon Weyl trace theorem.
import DASHI.Physics.Gravity.KSW668AdS5OriginalRadialSobolevPowerReuseExact

-- F8 X: ORIGINAL a=t TT angular yy source 0/2/4 is exactly the
-- Base369.TriTruth unsigned 0/1/2 *index* (ell=2q, radial d=3+4q).
-- Exact source Legendre weights/receiver axis, source-producer consumer;
-- explicit C3 label-rotation radial non-intertwiner. Not physical C3,
-- not 3/6/9 gravity dimensions, not dual-Weyl convergence or Agda kernel.
import DASHI.Physics.Gravity.KSW668AdS5TTUnbalancedTernary369ConsumerExact

-- F8 XI: original weak Israel SAT global C boundary Udot-only repair
-- has exact SBP2 left-null parity obstruction. Native n3/n4 rational
-- column certificates; general n symbolic recurrence checked in Python.
-- Joint P/M/U energy-compatible SAT and continuum Weyl remain OPEN.
import DASHI.Physics.Gravity.KSW668AdS5TTWeakIsraelSBPLeftNullParityExact

-- KSW XII exact radial dimension-raising ladder L_(d+2) J=J L_d
-- (d3->7->11): the three-channel nilpotent commuting shift has
-- genuine supplied differential intertwiner premises. NOT an
-- invertible C3 rotation or a physical original sourced Weyl action.
-- Optional chosen Z3 Weil SL2Z modular S/T is source-level SymPy
-- tested, but DOES NOT commute with the original radial generator.
-- Monster min nontrivial complex rep 196883 forbids a whole-Monster
-- nontrivial 3D index action; z is KK normal, not spatial radial r.
import DASHI.Physics.Gravity.KSW668AdS5TTModularRadialLadderConsumerExact
