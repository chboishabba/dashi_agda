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
