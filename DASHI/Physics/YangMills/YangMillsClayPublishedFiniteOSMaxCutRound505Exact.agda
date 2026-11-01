{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMaxCutRound505Exact where

------------------------------------------------------------------------
-- GOAL-1 A / ROUND505: PUBLISHED FINITE OS SOURCE MAX-CUT
--
-- The published/standard source theorems are already authority-owned.  The
-- physical YM payments are their literal attachment to the SAME finite CMP119
-- family:
--
--   F1 whole-lattice Euclidean covariance -> literal CMP119 action/observables;
--   F2 bosonic permutation symmetry -> literal CMP119 observable algebra;
--   F3 published Wilson reflection positivity -> literal finite OS2 carrier.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as RP
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462

round505FiniteOSAssemblyCompilerLevel : ProofLevel
round505FiniteOSAssemblyCompilerLevel =
  R462.round462PublishedFiniteOSCompilerLevel

round505EuclideanSourceAuthorityLevel : ProofLevel
round505EuclideanSourceAuthorityLevel =
  Euclidean.cmp119WholeLatticeEuclideanCovarianceSourceLevel

round505BosonicSourceAuthorityLevel : ProofLevel
round505BosonicSourceAuthorityLevel =
  Bosonic.bosonicPermutationSymmetrySourceLevel

round505WilsonRPAuthorityLevel : ProofLevel
round505WilsonRPAuthorityLevel =
  RP.round461PublishedWilsonRPAuthorityLevel

literalRound505EuclideanSameObjectAttachmentLevel : ProofLevel
literalRound505EuclideanSameObjectAttachmentLevel =
  Euclidean.literalCMP119WholeLatticeEuclideanAttachmentLevel

literalRound505BosonicSameObjectAttachmentLevel : ProofLevel
literalRound505BosonicSameObjectAttachmentLevel =
  Bosonic.literalCMP119BosonicObservableAttachmentLevel

literalRound505WilsonRPSameObjectAttachmentLevel : ProofLevel
literalRound505WilsonRPSameObjectAttachmentLevel =
  RP.literalRound461PublishedWilsonSameObjectApplicationLevel
