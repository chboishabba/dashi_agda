module DASHI.Biology.DrosophilaGauthey2PSelectionRecoveryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-level recovery architecture for the pooled conventional-2p matrix.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- analysis code github:murthylab/lightbead-analysis.
--
-- Source code establishes:
-- * four conventional-2p trials;
-- * 47 z-slices per trial;
-- * 1000 independently clustered supervoxels per slice;
-- * dffs_corrected[:, :668] per trial;
-- * vertical ROI-row concatenation across trials;
-- * top 0.5 percent row selection;
-- * export of selected traces without selected source indices.
--
-- A complete runtime audit of the deposited Data.zip subsequently established
-- that the four source trial pickles and four corresponding n1000 label files
-- are absent from that deposit. Exact trace-row recovery therefore remains a
-- valid conditional compiler but cannot fire on the deposited source set.
------------------------------------------------------------------------

record TwoPSelectionSourceReceipt : Set where
  constructor twoPSelectionSourceReceipt
  field
    trialCount : Nat
    planesPerTrial : Nat
    clustersPerPlane : Nat
    candidateROIRows : Nat
    timeSamples : Nat
    selectionNumeratorPerThousand : Nat
    selectedROIRows : Nat
    depositedRowsAreSelectedROIs : Bool
    depositedColumnsAreTimeSamples : Bool
    selectedSourceIndicesExported : Bool

open TwoPSelectionSourceReceipt public

canonicalTwoPSelectionSourceReceipt : TwoPSelectionSourceReceipt
canonicalTwoPSelectionSourceReceipt =
  twoPSelectionSourceReceipt
    4 47 1000 188000 668 5 940 true true false

record SourceRowCoordinate : Set where
  constructor sourceRowCoordinate
  field
    globalSourceRow : Nat
    trialOrdinal : Nat
    planeIndex : Nat
    clusterIndex : Nat
    sourceTrialIdentifier : String
    sourceLabelIdentifier : String

open SourceRowCoordinate public

record SourceRecoveryBoundary : Set where
  constructor sourceRecoveryBoundary
  field
    selectedTraceDoesNotCarrySourceIndexByItself : Bool
    exactTraceMatchCanRecoverSourceIndexConditionally : Bool
    recoveredGlobalRowDeterminesTrialPlaneCluster : Bool
    planeLocalClusterIdentityIsNotGlobalIntegerLabelIdentity : Bool
    recoveryRequiresOriginalFourSourceTrialMatrices : Bool
    completeUnambiguousRecoveryRequiredForPromotion : Bool
    depositedSourceSetDoesNotContainRequiredGeneratingInputs : Bool
    conditionalCompilerDoesNotImplyRunnableDepositRoute : Bool
    recoveredSupervoxelStillDoesNotImplyMaleCNSNeuronIdentity : Bool

open SourceRecoveryBoundary public

canonicalSourceRecoveryBoundary : SourceRecoveryBoundary
canonicalSourceRecoveryBoundary =
  sourceRecoveryBoundary true true true true true true true true true

record SourceRecoveryAssessment : Set where
  constructor sourceRecoveryAssessment
  field
    sourceTrialsPresent : Bool
    exactTraceRowsMatched : Bool
    noAmbiguousRows : Bool
    all940Recovered : Bool
    sourceROIIdentityAdmissible : Bool
    externalScientificReceiptRequired : Bool
    sameAnimalMaleCNSIdentityAdmissible : Bool

open SourceRecoveryAssessment public

closedNegativeDepositRecoveryAssessment : SourceRecoveryAssessment
closedNegativeDepositRecoveryAssessment =
  sourceRecoveryAssessment false false false false false true false
