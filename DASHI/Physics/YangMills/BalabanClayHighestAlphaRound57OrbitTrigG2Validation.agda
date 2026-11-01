module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57OrbitTrigG2Validation where

------------------------------------------------------------------------
-- ROUND 57 FOCUSED VALIDATION ROOT
--
-- This root deliberately imports ONLY the high-information producer reductions
-- advanced in Round57 and the existing active-scale bridge they feed.  It does
-- not import continuum/OS placeholders and does not turn remaining physical
-- estimates into authority fields.
--
-- Main sources used by the imported modules:
--
-- Kenneth G. Wilson, "Confinement of Quarks", Phys. Rev. D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- L. D. Faddeev and V. N. Popov, "Feynman Diagrams for the Yang--Mills
-- Field", Phys. Lett. B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
--
-- L. F. Abbott, "The Background Field Method Beyond One Loop", Nucl. Phys.
-- B 185 (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Commun. Math. Phys. 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban, "Convergent Renormalization Expansions for Lattice Gauge
-- Theories", Commun. Math. Phys. 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Commun. Math. Phys. 122
-- (1989), 355--392. DOI: 10.1007/BF01238433.
--
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Möbius Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- Marc Daumas, David Lester and César Muñoz, "Verified Real Number
-- Calculations: A Library for Interval Arithmetic", IEEE Trans. Computers 58
-- (2009), 226--237. DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022,
-- arXiv:2205.08354. No DOI assigned.
------------------------------------------------------------------------

-- L3: generated hypercubic geometry, exact action, four-orbit reduction and
-- cancellation-preserving orbit sums.
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitQuadratureWeightsExact
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact
import DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact
import DASHI.Physics.YangMills.BalabanCMP109FourOrbitNormalizedQuadratureExact

-- Source (5.6)/(5.7) Euclidean covariance of the FULL CMP109 vacuum
-- polarization tensor feeds the concrete signed-permutation generators.
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact

-- L3: safe syntax normalization and Bishop semantic interval arithmetic.
-- Hat momentum is reduced to the literal Wilson sine-half definition rather
-- than independently certified.
import DASHI.Physics.YangMills.BalabanClayT4DiagramTrigNormalFormExact
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact
import DASHI.Physics.YangMills.BalabanClayT4BishopPositiveReciprocalIntervalExact
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact

-- G2: exact Boolean-four-cube degree grouping and joint grouped interval
-- transport after the pre-existing exact owner cancellation.
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact

-- L4: same physical five H-R_beta channels, now reduced to exact fourth-order
-- factorization plus quotient majorants before feeding the Round56 summation.
import DASHI.Physics.YangMills.BalabanYM4FiveChannelFourthOrderFactorizationExact

-- L5/L6: source-native CMP119 E/R/B complete-density state, plus the existing
-- active-scale CMP122 Theorem-1 / finite-beta bridge (not duplicated here).
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact

-- Nonblocking foundation lane.  The arctangent series are actual convergent
-- Bishop series; their cubic/quintic interlacing now proves
--
--                3 < pi_M < 22/7
--
-- for the constructed Machin real.  Hence the only pi-facing physical leaf is
-- identification of the Wilson Fourier period with this same real.
import DASHI.Foundations.BishopMachinRationalTangentAlgebraExact
import DASHI.Foundations.BishopMachinArctanConstructionExact
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact
import DASHI.Foundations.BishopArctanCubicQuinticPolynomialExact
import DASHI.Foundations.BishopMachinPiRationalWindowExact
import DASHI.Physics.YangMills.BalabanBishopMachinNormalizedOuterMomentumExact
