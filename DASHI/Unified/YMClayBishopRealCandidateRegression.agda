module DASHI.Unified.YMClayBishopRealCandidateRegression where

-- YM.REAL original-source candidate regression.
-- NOT --safe: several upstream Bishop complex / legacy scalar bridge owners
-- are currently non-safe. Never import this module from the Golden --safe
-- TOE root; the safe finite algebra modules are separately imported there.
--
-- Aggregation, not a proof of Haar, exact original Wilson source identity,
-- or kernel acceptance. This regression explicitly retains the source seam.
-- Prior owner attribution: Wilson, Balaban, Fejer, Stroud, Bishop,
-- Murray/Csimma and the repository's original matrix/finite-bond owners.

import DASHI.Physics.YangMills.YMClaySU2FejerProductFiniteExact
  as FejerFinite
import DASHI.Physics.YangMills.YMClayBishopFiniteWeightedIntegralLawsExact
  as WeightedFinite
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact
  as QuaternionTrace
import DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact
  as QuaternionDeterminant
import DASHI.Physics.YangMills.YMClayBishopSU2UnitarityExact
  as QuaternionUnitarity
import DASHI.Physics.YangMills.YMClayBishopSU2HaarSeriesLimitExact
  as ConstructiveCauchy
import DASHI.Physics.YangMills.YMClayBishopFiniteWilsonNormalizedExact
  as FiniteWilson

-- Pi: algebraic last-mile of quarter-angle bridge, analytic inputs OPEN.
import DASHI.Foundations.BishopMachinPiDoubleAngleAlgebraExact
  as BishopMachinDoubleAngle

-- True selected Round11 sine/cosine and Machin pi; analytic quarter input open.
import DASHI.Foundations.BishopMachinPiPeriodFromQuarterExact
  as BishopMachinSameSourcePeriod

-- Positive finite Bishop Wilson construction; original periodic Haar still OPEN.
import DASHI.Physics.YangMills.YMClayBishopWilsonGibbsPositiveExact
  as BishopWilsonGibbsPositiveExact

-- Positive finite Bishop Wilson construction; original periodic Haar still OPEN.
import DASHI.Physics.YangMills.YMClayBishopSU2WilsonDeficitPositiveExact
  as BishopSU2WilsonDeficitPositiveExact

-- Positive finite Bishop Wilson construction; original periodic Haar still OPEN.
import DASHI.Physics.YangMills.YMClayBishopSU2FiniteGibbsPartitionExact
  as BishopSU2FiniteGibbsPartitionExact

-- Canonical rational-to-Bishop SU2 trace source, group/Haar still open.
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2ToBishopTraceExact
  as OriginalRationalSU2BishopTrace

-- Actual original rational norm -> Bishop unit matrix, pending Agda acceptance.
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2BishopUnitaryWeldExact
  as OriginalRationalSU2BishopUnitary
