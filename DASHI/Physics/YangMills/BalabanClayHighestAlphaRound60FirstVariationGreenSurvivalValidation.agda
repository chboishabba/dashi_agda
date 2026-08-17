module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60FirstVariationGreenSurvivalValidation where

------------------------------------------------------------------------
-- ROUND 60 FOCUSED VALIDATION ROOT
--
-- This tranche returns to the shortest physical Clay cutset after Round59's
-- continuum-gap architecture.  It closes the A1 source-support seam, derives
-- positivity of the SAME finite KKT Gram pseudoinverse already used by G2,
-- collapses A2's sixteen signed Green lower bounds to eight diagonal energies,
-- and makes asymptotic freedom an explicit upstream gate for continuum
-- nontriviality.  It also corrects the spectral branch so reversibility is not
-- forced when Lawler--Sokal's nonreversible/killed regimes fit the literal RG
-- kernel better, and records Chen--Wang's unbounded symmetric-form route.
--
-- No module below promotes the still-open selected-region diagonal energy
-- bounds, raw/charge endpoint, literal Wilson/ghost/Haar coefficient, five
-- physical g^4 channels, continuum Schwinger construction, OS passage,
-- interacting survival, physical clustering, or reconstruction.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound59PositiveRGGeometryValidation

-- A1: actual Wilson first variation = four literal noncommutative product-rule
-- atoms, evaluated on the four-boundary constrained coordinate basis and
-- canonically zero-extended to the full physical carrier.
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact

-- A2/G2 endpoint: Moore--Penrose + K=L L* proves K+ positive semidefinite
-- exactly.  Polarization derives all sixteen signed degree-pair lower bounds
-- from only four source and four defect diagonal K+ energies.  The canonical
-- weld proves these are the SAME G2 degree blocks, and the final compiler turns
-- a literal 4 raw + 8 diagonal + charge selected-region dataset into the old
-- uniform 4+16 endpoint theorem automatically.
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact
import DASHI.Physics.YangMills.BalabanSelectedGreenDiagonalEndpointAdapterExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact
import DASHI.Physics.YangMills.BalabanUniformCanonicalDiagonalG2EnvelopeExact

-- F1/F2 theorem selection: Lawler--Sokal includes reversible,
-- nonreversible, and killed-process regimes.  If the continuum-adjacent
-- positive object is instead a symmetric but unbounded form, Chen--Wang is a
-- separate source-native route rather than an artificial boundedness receipt.
import DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact
import DASHI.Physics.YangMills.BalabanRGChenGeneralSymmetricFormBoundaryExact

-- E3 is downstream of B/C.  A nonzero perturbative survival margin after the
-- physical g^4 penalty is proved to remain a lower bound for physical beta,
-- but beta positivity is deliberately NOT identified with non-Gaussian
-- continuum survival.  The phi^4_4 triviality theorem is recorded as the
-- adversarial precedent for why that final implication must be proved.
import DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact
