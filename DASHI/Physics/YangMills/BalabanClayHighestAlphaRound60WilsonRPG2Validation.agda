module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60WilsonRPG2Validation where

------------------------------------------------------------------------
-- ROUND60 FOCUSED VALIDATION ROOT
--
-- G2 / A1-A2-A3 REDUCTION
--   literal four-atom Wilson first variation
--     -> actual basis-evaluated plaquette-support theorem
--     -> existing canonical subset/KKT/Mobius authority
--     -> K+ positivity from Moore--Penrose + K=L L*
--     -> polarization
--     -> Schur row-mass diagonal control
--     -> charge-relative 4 raw + 1 row + 8 norm^2 compiler.
--
--   The literal cross charge vanishes on the zero physical field, so an
--   unconditional positive absolute charge floor is not the homogeneous
--   theorem.  The preferred Round60 closure now proves ratios directly:
--
--     raw_d <= r_d Q,
--     ||S_d||^2 <= s_d Q,
--     ||D_d||^2 <= t_d Q,
--
--   and reduces G2 to one dimensionless coefficient gate
--
--     residualRatio <= 55 / 18874368.
--
--   No division by Q and no Q>0 premise is used.
--
-- ONE-LOOP / B1
--   construct the literal background Faddeev--Popov operator M_A=D_A G_A;
--   at identity background prove the periodic nearest-neighbour Laplacian;
--   expose the exact global-gauge constant zero mode;
--   keep finite side-four Fourier modes distinct from the generated 4^4
--   Brillouin BOX partition;
--   strengthen the physical trig carrier with same-momentum half-angle
--   coherence and prove the free ghost symbol equals the existing Wilson
--   hat{k}^2 atom.
--
--   Remaining ghost theorem: source-specific infinite-lattice/background
--   Fourier identification, global-gauge reduction/pseudodeterminant, then the
--   determinant/log-det colour/orbit contribution.
--
-- HYPERCUBIC / WALSH METHOD IDENTIFICATION
--   the generated four sign flips + three adjacent transpositions are the
--   standard B4=(C2)^4 semidirect S4 hypercubic generator families;
--   Walsh--Fourier terminology/orthogonality is anchored to O'Donnell;
--   Luescher--Weisz coordinate-space recursion is cited as related lattice
--   perturbation methodology but NOT identified with the finite box quotient.
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
-- SOURCE CHAIN
--   CMP116 is explicitly registered as the cluster-expansion bridge between
--   CMP109 small-field effective-action generation and later complete-density
--   / R-operation theorems.  It is not used as a continuum substitute.
--
-- NONTRIVIALITY GUARD
--   a controlled one-loop-minus-higher-order margin implies positive physical
--   beta, but interacting continuum survival remains a separate theorem.
--
-- SOURCE METADATA (selected)
--   Wilson: DOI 10.1103/PhysRevD.10.2445
--   Faddeev--Popov: DOI 10.1016/0370-2693(67)90067-6
--   Luescher--Weisz 1986: DOI 10.1016/0550-3213(86)90094-5
--   Luescher--Weisz 1995: DOI 10.1016/0550-3213(95)00185-U
--   Capitani: DOI 10.1016/S0370-1573(03)00211-4
--   Goeckeler et al. hypercubic group: DOI 10.1103/PhysRevD.54.5705
--   O'Donnell: DOI 10.1017/CBO9781139814782
--   O'Donnell Ch.1: DOI 10.1017/CBO9781139814782.002
--   Bałaban CMP99: DOI 10.1007/BF01240355
--   Bałaban CMP102: DOI 10.1007/BF01229381
--   Bałaban CMP109: DOI 10.1007/BF01215223
--   Bałaban CMP116: DOI 10.1007/BF01239022
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
import DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalSchurNormG2ClosureExact

import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovGlobalGaugeZeroModeExact
import DASHI.Physics.YangMills.BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact
import DASHI.Physics.YangMills.BalabanClayT4HypercubicLatticePerturbationMethodExact
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToCombinedRGExact

import DASHI.Physics.YangMills.BalabanWilsonLatticeReflectionPositivityExact
import DASHI.Physics.YangMills.BalabanPositiveKernelReflectionPositivityNoGoExact
import DASHI.Physics.YangMills.BalabanReflectionPositiveCoarseGrainingTransportExact

import DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact
import DASHI.Physics.YangMills.BalabanRGChenWangSymmetricFormGapBoundaryExact

import DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact
