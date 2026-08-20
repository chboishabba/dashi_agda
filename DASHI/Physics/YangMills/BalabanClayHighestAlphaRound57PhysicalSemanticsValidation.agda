module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57PhysicalSemanticsValidation where

------------------------------------------------------------------------
-- ROUND 57 PHYSICAL-SEMANTICS VALIDATION ROOT
--
-- This extends the initial Round57 root with the later high-alpha advances:
--   * CMP109 source (5.6),(5.7) symmetry -> generated hypercubic action;
--   * exact normalized four-orbit quadrature 4,6,4,1;
--   * exact Bishop four-corner product without real trichotomy;
--   * positive Bishop reciprocal/division interval semantics;
--   * compositional actual-Bishop-value/rational-certificate expressions;
--   * canonical SU(2)/Feynman-gauge atom environment deriving hat{k}^2 from
--     the literal Wilson sine-half definition;
--   * concrete convergent Machin arctangent interlacing.
--
-- Source provenance is recorded in each imported producer module.  In
-- particular Bałaban CMP109 is Commun. Math. Phys. 109 (1987), 249--301,
-- DOI 10.1007/BF01215223; Bishop--Bridges, Constructive Analysis (1985),
-- DOI 10.1007/978-3-642-61667-9; Murray, Constructive Analysis in the Agda
-- Proof Assistant (2022), arXiv:2205.08354, no DOI assigned.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57OrbitTrigG2Validation

import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact
import DASHI.Physics.YangMills.BalabanCMP109FourOrbitNormalizedQuadratureExact

import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact
import DASHI.Physics.YangMills.BalabanClayT4BishopPositiveReciprocalIntervalExact
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact

import DASHI.Foundations.BishopArctanHalfBallInterlacingExact
