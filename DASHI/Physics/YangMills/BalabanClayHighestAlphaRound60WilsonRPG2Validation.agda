module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60WilsonRPG2Validation where

------------------------------------------------------------------------
-- ROUND60 FOCUSED VALIDATION ROOT
--
-- This tranche advances three genuine theorem fronts on top of Round59:
--
-- G2 / A1-A2
--   literal four-atom Wilson first variation
--     -> actual basis-evaluated plaquette-support theorem
--     -> existing canonical subset/KKT/Moebius authority
--     -> K+ positivity from Moore--Penrose + K=L L*
--     -> polarization
--     -> Schur row-mass diagonal control
--     -> uniform 4 raw + 1 row + 8 norm^2 + charge compiler.
--
--   The literal cross charge vanishes on the zero physical field.  Hence an
--   absolute strictly-positive charge floor is valid only after normalization
--   or quantitative exclusion of zero; otherwise the final G2 bound should be
--   formulated charge-relatively.
--
-- REFLECTION POSITIVITY
--   Osterwalder--Seiler / Menotti--Pelissetto Wilson lattice RP is imported at
--   the literature boundary;
--   finite reflection-square positivity is proved locally;
--   RP transports through reflection-compatible coarse graining;
--   positive RG transition weights are proved NOT to imply RP by an exact
--   two-state counterexample.
--
-- RG SPECTRAL ROUTE
--   Lawler--Sokal is no longer hard-wired to reversibility: reversible,
--   nonreversible and killed regimes are explicit;
--   Chen--Wang is available as the alternative general symmetric-form route.
--   Only one physical spectral route is required.
--
-- NONTRIVIALITY GUARD
--   a controlled one-loop-minus-higher-order margin implies positive physical
--   beta, but interacting continuum survival remains a separate theorem.
--
-- SOURCE METADATA
--   Wilson: DOI 10.1103/PhysRevD.10.2445
--   Bałaban CMP99: DOI 10.1007/BF01240355
--   Bałaban CMP102: DOI 10.1007/BF01229381
--   Penrose: DOI 10.1017/S0305004100030401
--   Horn--Johnson: DOI 10.1017/CBO9781139020411
--   Osterwalder--Seiler: DOI 10.1016/0003-4916(78)90039-8
--   Menotti--Pelissetto: DOI 10.1007/BF01221251
--   Lawler--Sokal: DOI 10.1090/S0002-9947-1988-0930082-9
--   Chen--Wang: DOI 10.1214/aop/1019160118
--   Gross--Wilczek: DOI 10.1103/PhysRevLett.30.1343
--   Politzer: DOI 10.1103/PhysRevLett.30.1346
--   Aizenman--Duminil-Copin: DOI 10.4007/annals.2021.194.1.3
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound59PositiveRGGeometryValidation

import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact
import DASHI.Physics.YangMills.BalabanUniformCanonicalSchurNormG2ClosureExact
import DASHI.Physics.YangMills.BalabanPlaquetteCrossChargeZeroFloorNoGoExact

import DASHI.Physics.YangMills.BalabanWilsonLatticeReflectionPositivityExact
import DASHI.Physics.YangMills.BalabanPositiveKernelReflectionPositivityNoGoExact
import DASHI.Physics.YangMills.BalabanReflectionPositiveCoarseGrainingTransportExact

import DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact
import DASHI.Physics.YangMills.BalabanRGChenWangSymmetricFormGapBoundaryExact

import DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact
