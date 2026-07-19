module DASHI.Physics.Closure.PenguinDecaySourceCoherenceLaw where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.PenguinDecayEmpiricalCandidateDiagnostic as Diagnostic
import DASHI.Physics.Closure.PenguinDecayLHCbChecksumAcceptedResidualReceipt as LHCb

------------------------------------------------------------------------
-- Dataset-source coherence for the penguin empirical lane.
--
-- The empirical stack now contains several legitimate but distinct artifacts:
--
--   * the selected 2021 LHCb/CDS supplementary archive;
--   * the later full Run-1+2 P5' value/covariance route;
--   * the CMS comparison route.
--
-- A checksum proves identity of one artifact.  It does not permit values,
-- covariance, residuals, and provenance from different source epochs to be
-- silently combined.  This law makes that missing comparison invariant
-- explicit and rejects mixed-source bundles by construction.


data PenguinDatasetLane : Set where
  lhcb2021SelectedThread : PenguinDatasetLane
  lhcb2025FullRunOneRunTwo : PenguinDatasetLane
  cms2023Comparison : PenguinDatasetLane

record PenguinProjectionSourceBundle : Set where
  constructor mkPenguinProjectionSourceBundle
  field
    provenanceLane : PenguinDatasetLane
    valueTableLane : PenguinDatasetLane
    covarianceLane : PenguinDatasetLane
    residualVectorLane : PenguinDatasetLane

open PenguinProjectionSourceBundle public

data SourceCoherent : PenguinProjectionSourceBundle → Set where
  coherentBundle :
    (lane : PenguinDatasetLane) →
    SourceCoherent
      (mkPenguinProjectionSourceBundle lane lane lane lane)

selectedThreadSupplementaryOnlyBundle :
  PenguinProjectionSourceBundle
selectedThreadSupplementaryOnlyBundle =
  mkPenguinProjectionSourceBundle
    lhcb2021SelectedThread
    lhcb2021SelectedThread
    lhcb2021SelectedThread
    lhcb2021SelectedThread

fullRunOneRunTwoBundle :
  PenguinProjectionSourceBundle
fullRunOneRunTwoBundle =
  mkPenguinProjectionSourceBundle
    lhcb2025FullRunOneRunTwo
    lhcb2025FullRunOneRunTwo
    lhcb2025FullRunOneRunTwo
    lhcb2025FullRunOneRunTwo

mixedSelectedThreadRunOneRunTwoBundle :
  PenguinProjectionSourceBundle
mixedSelectedThreadRunOneRunTwoBundle =
  mkPenguinProjectionSourceBundle
    lhcb2021SelectedThread
    lhcb2025FullRunOneRunTwo
    lhcb2025FullRunOneRunTwo
    lhcb2025FullRunOneRunTwo

selectedThreadBundleSourceCoherent :
  SourceCoherent selectedThreadSupplementaryOnlyBundle
selectedThreadBundleSourceCoherent =
  coherentBundle lhcb2021SelectedThread

fullRunOneRunTwoBundleSourceCoherent :
  SourceCoherent fullRunOneRunTwoBundle
fullRunOneRunTwoBundleSourceCoherent =
  coherentBundle lhcb2025FullRunOneRunTwo

mixedSelectedThreadRunOneRunTwoBundleRejected :
  SourceCoherent mixedSelectedThreadRunOneRunTwoBundle →
  ⊥
mixedSelectedThreadRunOneRunTwoBundleRejected ()

------------------------------------------------------------------------
-- Artifact-kind boundary.
--
-- The selected-thread checksum currently bound in the repository is a real
-- supplementary-archive checksum.  It is not definitionally a value table,
-- covariance table, or residual-vector artifact.  This is why the diagnostic
-- may truthfully record the supplementary checksum while still withholding
-- dataset authority and empirical promotion.

record SelectedThreadChecksumKindBoundary : Setω where
  field
    lhcbReceipt :
      LHCb.LHCbChecksumAcceptedResidualSurfaceReceipt

    selectedThreadSupplementaryChecksumPresent :
      LHCb.selectedThreadSupplementaryChecksumPresent lhcbReceipt
      ≡
      true

    supplementaryArtifactIsNotValueTable :
      LHCb.artifactIsValueTableReceipt
        (LHCb.lhcbSupplementaryChecksumBinding lhcbReceipt)
      ≡
      false

    supplementaryArtifactIsNotCovarianceTable :
      LHCb.artifactIsCovarianceTableReceipt
        (LHCb.lhcbSupplementaryChecksumBinding lhcbReceipt)
      ≡
      false

    supplementaryArtifactIsNotResidualVector :
      LHCb.artifactIsResidualVector
        (LHCb.lhcbSupplementaryChecksumBinding lhcbReceipt)
      ≡
      false

open SelectedThreadChecksumKindBoundary public

canonicalSelectedThreadChecksumKindBoundary :
  SelectedThreadChecksumKindBoundary
canonicalSelectedThreadChecksumKindBoundary =
  record
    { lhcbReceipt =
        LHCb.canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
    ; selectedThreadSupplementaryChecksumPresent =
        refl
    ; supplementaryArtifactIsNotValueTable =
        refl
    ; supplementaryArtifactIsNotCovarianceTable =
        refl
    ; supplementaryArtifactIsNotResidualVector =
        refl
    }

------------------------------------------------------------------------
-- Integrated fail-closed source-coherence gate.

record PenguinSourceCoherenceDiagnostic : Setω where
  field
    empiricalDiagnostic :
      Diagnostic.PenguinDecayEmpiricalCandidateDiagnostic

    empiricalDiagnosticIsCanonical :
      empiricalDiagnostic
      ≡
      Diagnostic.canonicalPenguinDecayEmpiricalCandidateDiagnostic

    selectedThreadChecksumKindBoundary :
      SelectedThreadChecksumKindBoundary

    runOneRunTwoSourceBundle :
      PenguinProjectionSourceBundle

    runOneRunTwoSourceBundleIsCanonical :
      runOneRunTwoSourceBundle
      ≡
      fullRunOneRunTwoBundle

    runOneRunTwoSourceCoherence :
      SourceCoherent runOneRunTwoSourceBundle

    mixedSourceBundleCannotPromote :
      SourceCoherent mixedSelectedThreadRunOneRunTwoBundle →
      ⊥

    sourceCoherenceGateReached :
      Bool

    sourceCoherenceGateReachedIsTrue :
      sourceCoherenceGateReached ≡ true

    empiricalPromotionStillBlocked :
      Diagnostic.empiricalPromotion empiricalDiagnostic
      ≡
      false

open PenguinSourceCoherenceDiagnostic public

canonicalPenguinSourceCoherenceDiagnostic :
  PenguinSourceCoherenceDiagnostic
canonicalPenguinSourceCoherenceDiagnostic =
  record
    { empiricalDiagnostic =
        Diagnostic.canonicalPenguinDecayEmpiricalCandidateDiagnostic
    ; empiricalDiagnosticIsCanonical =
        refl
    ; selectedThreadChecksumKindBoundary =
        canonicalSelectedThreadChecksumKindBoundary
    ; runOneRunTwoSourceBundle =
        fullRunOneRunTwoBundle
    ; runOneRunTwoSourceBundleIsCanonical =
        refl
    ; runOneRunTwoSourceCoherence =
        fullRunOneRunTwoBundleSourceCoherent
    ; mixedSourceBundleCannotPromote =
        mixedSelectedThreadRunOneRunTwoBundleRejected
    ; sourceCoherenceGateReached =
        true
    ; sourceCoherenceGateReachedIsTrue =
        refl
    ; empiricalPromotionStillBlocked =
        refl
    }

canonicalPenguinSourceCoherenceGateReached :
  sourceCoherenceGateReached canonicalPenguinSourceCoherenceDiagnostic
  ≡
  true
canonicalPenguinSourceCoherenceGateReached =
  refl

canonicalPenguinMixedSourcePromotionRejected :
  SourceCoherent mixedSelectedThreadRunOneRunTwoBundle →
  ⊥
canonicalPenguinMixedSourcePromotionRejected =
  mixedSourceBundleCannotPromote canonicalPenguinSourceCoherenceDiagnostic
