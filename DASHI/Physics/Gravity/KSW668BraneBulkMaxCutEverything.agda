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
