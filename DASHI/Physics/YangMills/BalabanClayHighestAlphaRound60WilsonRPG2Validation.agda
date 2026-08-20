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
--   theorem. The preferred Round60 closure proves ratios directly:
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
--   construct an exact anchored gauge-orbit section removing those constant
--   modes while leaving the flat FP operator unchanged;
--   keep finite side-four Fourier modes distinct from the generated 4^4
--   Brillouin BOX partition;
--   strengthen the physical trig carrier with same-momentum half-angle
--   coherence and prove the free ghost symbol equals the existing Wilson
--   hat{k}^2 atom.
--
--   Remaining ghost theorem: prove no further kernel on the reduced/anchored
--   carrier, construct the reduced determinant/log-det background expansion,
--   and identify its colour/orbit contribution on the physical one-loop carrier.
--
-- HYPERCUBIC / WALSH METHOD IDENTIFICATION
--   the generated four sign flips + three adjacent transpositions are the
--   standard B4=(C2)^4 semidirect S4 hypercubic generator families;
--   Walsh--Fourier terminology/orthogonality is anchored to O'Donnell;
--   Luescher--Weisz coordinate-space recursion is cited as related lattice
--   perturbation methodology but NOT identified with the finite box quotient.
--
-- REFLECTION POSITIVITY / TRANSFER OPERATOR
--   Osterwalder--Seiler / Menotti--Pelissetto Wilson lattice RP is imported at
--   the literature boundary;
--   Luescher's Wilson transfer matrix is imported as self-adjoint and strictly
--   positive;
--   exact OS pullback/recombination is welded to the older
--   ReflectionPositiveBlocking theorem;
--   compatible blockings compose, so finite-scale OS2 need not be reproved at
--   every RG depth once the literal one-step Bałaban OS pullback is identified;
--   positive RG transition weights are still NOT identified with RP or with
--   Luescher's transfer operator without a source-native same-object theorem.
--
-- TWO SPECTRAL ROUTES, ONE NEEDED
--   Route A (Round59): literal positive RG geometry -> Lawler--Sokal or
--   Chen--Wang -> cutoff-uniform RG gap -> physical metric/clustering bridge.
--
--   Route B (Round60 direct transfer): Luescher Wilson transfer operator +
--   literal Balaban/transfer compatibility -> physical Schur/Feshbach one-step
--   gap estimates -> terminal gap pullback. The pullback algebra now proves the
--   STRICT endpoint
--
--     discountedLossBudget < 2^-N terminalGap
--       -> 0 < pulledBackGap <= fineGap.
--
--   Route B may therefore bypass the auxiliary Cheeger kernel if its physical
--   compatibility and one-step loss hypotheses can be proved. No equality
--   between the two spectral routes is assumed.
--
-- SOURCE CHAIN
--   CMP116 is explicitly registered as the cluster-expansion bridge between
--   CMP109 small-field effective-action generation and later complete-density
--   / R-operation theorems. It is not used as a continuum substitute.
--
-- CONTINUUM / RECONSTRUCTION
--   Glimm--Jaffe is the imported reconstruction authority together with the
--   original Osterwalder--Schrader papers. The repository endpoint explicitly
--   retains an interacting-continuum witness: reconstruction or a positive gap
--   cannot manufacture nontriviality.
--
-- NONTRIVIALITY GUARD
--   a controlled one-loop-minus-higher-order margin implies positive physical
--   beta, but interacting continuum survival remains a separate theorem.
--
-- SOURCE METADATA (selected)
--   Wilson: DOI 10.1103/PhysRevD.10.2445
--   Faddeev--Popov: DOI 10.1016/0370-2693(67)90067-6
--   Luescher transfer matrix: DOI 10.1007/BF01614090
--   Luescher--Weisz 1986: DOI 10.1016/0550-3213(86)90094-5
--   Luescher--Weisz 1995: DOI 10.1016/0550-3213(95)00185-U
--   Capitani: DOI 10.1016/S0370-1573(03)00211-4
--   Goeckeler et al. hypercubic group: DOI 10.1103/PhysRevD.54.5705
--   O'Donnell: DOI 10.1017/CBO9781139814782
--   O'Donnell Ch.1: DOI 10.1017/CBO9781139814782.002
--   Bałaban CMP96: DOI 10.1007/BF01240221
--   Bałaban CMP99 gauge fixing: DOI 10.1007/BF01466594
--   Bałaban CMP99 propagators: DOI 10.1007/BF01240355
--   Bałaban CMP102: DOI 10.1007/BF01229381
--   Bałaban CMP109: DOI 10.1007/BF01215223
--   Bałaban CMP116: DOI 10.1007/BF01239022
--   Penrose: DOI 10.1017/S0305004100030401
--   Horn--Johnson: DOI 10.1017/CBO9781139020411
--   Osterwalder--Schrader I: DOI 10.1007/BF01645738
--   Osterwalder--Schrader II: DOI 10.1007/BF01608978
--   Osterwalder--Seiler: DOI 10.1016/0003-4916(78)90039-8
--   Menotti--Pelissetto: DOI 10.1007/BF01221251
--   Glimm--Jaffe 2nd ed.: DOI 10.1007/978-1-4612-4728-9
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
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovAnchoredGaugeReductionExact
import DASHI.Physics.YangMills.BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact
import DASHI.Physics.YangMills.BalabanClayT4HypercubicLatticePerturbationMethodExact
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToCombinedRGExact

import DASHI.Physics.YangMills.BalabanWilsonLatticeReflectionPositivityExact
import DASHI.Physics.YangMills.BalabanPositiveKernelReflectionPositivityNoGoExact
import DASHI.Physics.YangMills.BalabanReflectionPositiveCoarseGrainingTransportExact
import DASHI.Physics.YangMills.BalabanWilsonTransferBlockingExact
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact
import DASHI.Physics.YangMills.BalabanClayOSPullbackBlockingBridgeExact

import DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact
import DASHI.Physics.YangMills.BalabanRGChenWangSymmetricFormGapBoundaryExact
import DASHI.Physics.YangMills.BalabanPositiveRGDirichletGeometryExact

import DASHI.Physics.YangMills.BalabanP33EffectiveSchurGapStepExact
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact
import DASHI.Physics.YangMills.BalabanP33PhysicalGapScaleInvarianceExact

import DASHI.Physics.YangMills.BalabanOSMassGapClosure
import DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact
