module DASHI.Biology.DrosophilaGautheyROIIdentityRecoveryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaGautheyFunctionalTrajectoryProducerExact as Gauthey
import DASHI.Biology.BioacousticFlySnowballParetoBidiExact as Snowball

------------------------------------------------------------------------
-- GAUTHEY POOLED-ROI SOURCE-IDENTITY RECOVERY
--
-- The compact published 2P carrier preserves the selected functional traces
-- but drops the source selection indices.  The public preprocessing code is
-- nevertheless specific enough to reconstruct those indices from the four
-- aligned source-trial dictionaries without materialising the whole
-- 188000 x 668 matrix at once:
--
--   per-trial row correlation
--   -> concatenate 188000 scalar correlations
--   -> global top 0.5% = 940 rows
--   -> global-row quotient/remainder by 47000
--   -> trial + local row
--   -> quotient/remainder by 1000
--   -> plane + cluster.
--
-- Exact identity is promoted ONLY when the reconstructed selected 940 x 668
-- matrix is array-equal to the exact compact published carrier.  Reproducing
-- the algorithm without that same-object comparison remains a candidate.
------------------------------------------------------------------------

record GautheyROIRecoveryGeometry : Set where
  constructor gauthey-roi-recovery-geometry
  field
    sourceTrials : Nat
    planesPerTrial : Nat
    clustersPerPlane : Nat
    rowsPerTrial : Nat
    totalSourceRows : Nat
    selectionPercent : String
    selectedRows : Nat
    timeSamples : Nat
    orderingReference : String

open GautheyROIRecoveryGeometry public

canonicalRecoveryGeometry : GautheyROIRecoveryGeometry
canonicalRecoveryGeometry = gauthey-roi-recovery-geometry
  4 47 1000 47000 188000 "0.5%" 940 668
  "source alignment constructs rows plane-major from 47 slices with 1000 clusters each; preprocessing stacks the four canonical trials in declared list order"

sourceTrialOrder : List String
sourceTrialOrder =
  "GCaMP6f_12132024_a2_r2.pkl" ∷
  "GCaMP6f_12132024_a2_r3.pkl" ∷
  "GCaMP6f_12132024_a2_r4.pkl" ∷
  "GCaMP6f_12202024_a1_r2.pkl" ∷ []

record SourceEquivalentSelectionReceipt : Set where
  constructor source-equivalent-selection-receipt
  field
    preprocessingBlob : String
    functionsBlob : String
    stimulusConstructionReference : String
    calciumKernelReference : String
    correlationReference : String
    selectionReference : String
    memoryBoundedImplementationReference : String
    sameOrderingAsSourceRequired : Bool

open SourceEquivalentSelectionReceipt public

canonicalSelectionReceipt : SourceEquivalentSelectionReceipt
canonicalSelectionReceipt = source-equivalent-selection-receipt
  "39a4ae6739b9e13040b971469616e908df41f502"
  "436b785a2c33b12968c5645ff0118f4e5493cf10"
  "functions.create_stim on the exact 13 source blocks, with strict start<index<end semantics"
  "GCaMP6f rise=0.050 s, decay=0.140 s, one-second kernel, normalized to peak one"
  "per-row z-normalization; z-normalized convolved stimulus; zero-lag dot-product divided by time length"
  "remove NaN correlations, ascending argsort, retain final int(188000 * 0.5 / 100)=940 rows"
  "animalexic/scripts/gauthey_roi_identity_recovery_adapter.py computes correlations per trial, concatenates only scalar correlations, then fetches selected source rows"
  true

------------------------------------------------------------------------
-- Identity state stays typed.  A source-equivalent reconstruction is stronger
-- than an arbitrary guess, but it is still not exact identity until welded to
-- the compact published object.
------------------------------------------------------------------------

data PooledRowIdentityStatus : Set where
  reconstructionCandidate : PooledRowIdentityStatus
  exactSameObjectWelded : PooledRowIdentityStatus

record PooledRowIdentityReceipt : Set where
  constructor pooled-row-identity-receipt
  field
    status : PooledRowIdentityStatus
    sourceTrialDigestsReference : String
    compactCarrierDigestReference : String
    reconstructedCarrierDigestReference : String
    exactArrayEqualityChecked : Bool
    trialPlaneClusterIdentityPaid : Bool
    maleCNSNeuronIdentityPaid : Bool
    animalexicPromotionPaid : Bool

open PooledRowIdentityReceipt public

candidateIdentityReceipt : PooledRowIdentityReceipt
candidateIdentityReceipt = pooled-row-identity-receipt
  reconstructionCandidate
  "source trial SHA-256 values must be retained by the runtime receipt"
  "unpaid until exact compact carrier is supplied"
  "runtime reconstruction digest"
  false false false false

exactWeldedIdentityReceipt :
  String → String → String →
  PooledRowIdentityReceipt
exactWeldedIdentityReceipt trialDigests compactDigest reconstructedDigest =
  pooled-row-identity-receipt
    exactSameObjectWelded
    trialDigests
    compactDigest
    reconstructedDigest
    true true false false

------------------------------------------------------------------------
-- Bidi rule:
--
-- forward: exact source-equivalent reconstruction + exact compact equality
--          pays pooled-row -> source trial/plane/cluster identity;
-- reverse: any mismatch or missing compact carrier reopens that identity before
--          downstream anatomical registration or same-row mechanistic claims.
------------------------------------------------------------------------

record ROIIdentityBidi : Set where
  constructor roi-identity-bidi
  field
    forwardEvidence : String
    forwardPaidClaim : String
    reverseReopeningCondition : String
    reverseReopenedDependency : String
    exactCompactEqualityRequired : Bool
    exactCompactEqualityCreatesNeuronIdentity : Bool
    exactCompactEqualityCreatesCausality : Bool
    exactCompactEqualityCreatesPromotion : Bool

open ROIIdentityBidi public

canonicalROIIdentityBidi : ROIIdentityBidi
canonicalROIIdentityBidi = roi-identity-bidi
  "exact four source trial bytes + source-equivalent selection algorithm + reconstructed 940x668 carrier + exact published compact carrier"
  "pooled selected row index -> exact source trial / plane / cluster identity"
  "compact carrier absent, source bytes differ, algorithm/order differs, or reconstructed compact matrix is not exactly array-equal"
  "pooled selected row source identity"
  true false false false

------------------------------------------------------------------------
-- Current Pareto consequence.
------------------------------------------------------------------------

paretoOwner : String
paretoOwner = "DASHI.Biology.BioacousticFlySnowballParetoBidiExact"

paidTimebaseReceipt : Gauthey.GautheyTimebaseSourceReceipt
paidTimebaseReceipt = Gauthey.canonicalGautheyTimebaseSourceReceipt

nextParetoLeaf : Snowball.FrontierLeaf
nextParetoLeaf = Snowball.roiTrialPlaneIdentity

nextParetoLeafReading : String
nextParetoLeafReading =
  "The common conventional-2P protocol timebase is source-code paid. The first high-alpha same-object leaf is now exact pooled selected-row identity: acquire the four aligned source trial dictionaries and exact compact 940x668 carrier, replay the source-equivalent selection, and require array equality. Exact MaleCNS neuron registration remains a later, higher-identity-risk leaf."

record GautheyROIIdentityRecoveryBoundary : Set where
  constructor gauthey-roi-identity-recovery-boundary
  field
    algorithmReplayAlonePaysExactIdentity : Bool
    exactCompactEqualityPaysSourceRowIdentity : Bool
    sourceRowIdentityEqualsMaleCNSNeuronIdentity : Bool
    sourceRowIdentityEqualsAnatomicalRegistration : Bool
    sourceRowIdentityEqualsCausalNecessity : Bool
    sourceRowIdentityEqualsAnimalexicPromotion : Bool
    mismatchMustFailClosed : Bool
    acquisitionMayProceedOutOfDependencyOrder : Bool

canonicalGautheyROIIdentityRecoveryBoundary : GautheyROIIdentityRecoveryBoundary
canonicalGautheyROIIdentityRecoveryBoundary =
  gauthey-roi-identity-recovery-boundary
    false true false false false false true true
