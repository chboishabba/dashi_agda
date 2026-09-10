{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact where

------------------------------------------------------------------------
-- ROUND306 / SHORTEST CURRENT B CUT
--
-- The standard OS/spectral route means the detailed subgap spectral-measure
-- construction R287-R303 is not mandatory mathematical debt.  It remains a
-- valuable optional internal reconstruction/cross-check.
--
-- R296 + R278 + R304 reduce arbitrary-pair continuum exponential clustering to
-- one analytic source theorem plus time/support semantics.  R305 then isolates
-- the established clustering->spectrum theorem as standard-library authority.
--
-- Current YM-specific payments on this route:
--
--   G1. literal absolute two-J CMP116/CMP119 localization on the exact T5 state;
--   G2. physical Euclidean-time translation / bounded-observable / support-
--       distance semantics for arbitrary physical observable pairs;
--   G3. same reconstructed Hamiltonian: the concrete q=1/2 decay bound means
--       exponential decay at one strictly positive physical mass m*.
--
-- Standard-library payment (not new 4D YM analysis):
--
--   S1. exponential connected clustering at m*>0 implies spectral separation
--       above the vacuum by m* on that same reconstructed Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as R305

record Round306Boundary : Set where
  constructor round306-boundary
  field
    ymSpecificPhysicalCutHasThreeCoordinates : Bool
    ymSpecificPhysicalCutHasThreeCoordinatesIsTrue :
      ymSpecificPhysicalCutHasThreeCoordinates ≡ true

    detailedSubgapSpectralRouteMandatory : Bool
    detailedSubgapSpectralRouteMandatoryIsFalse :
      detailedSubgapSpectralRouteMandatory ≡ false

    arbitraryPairContinuumClusteringAfterG1G2CompilerOwned : Bool
    arbitraryPairContinuumClusteringAfterG1G2CompilerOwnedIsTrue :
      arbitraryPairContinuumClusteringAfterG1G2CompilerOwned ≡ true

    massGapAfterClusteringRateAndStandardTransferCompilerOwned : Bool
    massGapAfterClusteringRateAndStandardTransferCompilerOwnedIsTrue :
      massGapAfterClusteringRateAndStandardTransferCompilerOwned ≡ true

    standardSpectralTransferIsYangMillsSpecificNewAnalysis : Bool
    standardSpectralTransferIsYangMillsSpecificNewAnalysisIsFalse :
      standardSpectralTransferIsYangMillsSpecificNewAnalysis ≡ false

canonicalRound306Boundary : Round306Boundary
canonicalRound306Boundary =
  round306-boundary true refl false refl true refl true refl false refl

round306G1LiteralAbsoluteTwoJLocalizationLevel : ProofLevel
round306G1LiteralAbsoluteTwoJLocalizationLevel =
  R296.round296LiteralAbsoluteTwoJLocalizationLevel

round306G2PhysicalPairwiseTimeMeaningLevel : ProofLevel
round306G2PhysicalPairwiseTimeMeaningLevel =
  R304.round304PhysicalTimeTranslationDistanceMeaningLevel

round306G3PhysicalMassRateNormalizationLevel : ProofLevel
round306G3PhysicalMassRateNormalizationLevel =
  R305.round305PhysicalMassRateNormalizationLevel

round306StandardClusteringToSpectrumLevel : ProofLevel
round306StandardClusteringToSpectrumLevel =
  R305.round305StandardClusteringToSpectrumTransferLevel

round306PairwiseClusteringCompilerLevel : ProofLevel
round306PairwiseClusteringCompilerLevel =
  R304.round304PairwiseContinuumClusteringCompilerLevel

round306MassGapAssemblyLevel : ProofLevel
round306MassGapAssemblyLevel = R305.round305NormalizedMassGapAssemblyLevel
