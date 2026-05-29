module DASHI.Physics.Closure.YangMillsMassGapBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as YMGap
import DASHI.Physics.Boundaries.GribovResolutionAuthorityReceipt as Gribov
import DASHI.Physics.Boundaries.TopologicalMassGapInterpretation as Topological
import DASHI.Physics.Boundaries.YMConstructive5DProofReceipt as YM5D

------------------------------------------------------------------------
-- Yang-Mills mass-gap boundary surface.
--
-- This module records the typed boundary shape for the mass-gap lane.  It
-- reuses the existing finite-depth mass-gap receipt as the upstream anchor,
-- but it does not claim the continuum Clay theorem, the positive spectral
-- lower bound, or any terminal promotion.

data YangMillsMassGapBoundaryStatus : Set where
  boundaryOnlyNoPromotion :
    YangMillsMassGapBoundaryStatus

data YangMillsMassGapOpenObligation : Set where
  missingFiniteVolumeCoercivity :
    YangMillsMassGapOpenObligation

  missingReflectionPositivity :
    YangMillsMassGapOpenObligation

  missingTransferMatrixPositivity :
    YangMillsMassGapOpenObligation

  missingSpectralProjectionIsolation :
    YangMillsMassGapOpenObligation

  missingContinuumLimitStability :
    YangMillsMassGapOpenObligation

  missingInfiniteVolumeStability :
    YangMillsMassGapOpenObligation

canonicalYangMillsMassGapOpenObligations :
  List YangMillsMassGapOpenObligation
canonicalYangMillsMassGapOpenObligations =
  missingFiniteVolumeCoercivity
  ∷ missingReflectionPositivity
  ∷ missingTransferMatrixPositivity
  ∷ missingSpectralProjectionIsolation
  ∷ missingContinuumLimitStability
  ∷ missingInfiniteVolumeStability
  ∷ []

data YangMillsStoneHamiltonianGapOpenBlocker : Set where
  missingPhysicalStoneGeneratorEqualsYMHamiltonian :
    YangMillsStoneHamiltonianGapOpenBlocker

  missingSelfAdjointDomainForYMHamiltonianOnRealQuotient :
    YangMillsStoneHamiltonianGapOpenBlocker

  missingSelectedCarrierGapTransportToPhysicalSpectrum :
    YangMillsStoneHamiltonianGapOpenBlocker

canonicalYangMillsStoneHamiltonianGapOpenBlockers :
  List YangMillsStoneHamiltonianGapOpenBlocker
canonicalYangMillsStoneHamiltonianGapOpenBlockers =
  missingPhysicalStoneGeneratorEqualsYMHamiltonian
  ∷ missingSelfAdjointDomainForYMHamiltonianOnRealQuotient
  ∷ missingSelectedCarrierGapTransportToPhysicalSpectrum
  ∷ []

record YangMillsMassGapBoundaryReceipt : Setω where
  field
    upstreamMassGapReceipt :
      YMGap.BalabanRGMassGapReceiptSurface

    ymConstructive5DExternalCandidate :
      YM5D.YMConstructive5DProofReceipt

    gribovResolutionExternalCandidate :
      Gribov.GribovResolutionAuthorityReceipt

    topologicalMassGapExternalCandidate :
      Topological.TopologicalMassGapInterpretationReceipt

    externalCandidateEvidencePromoted :
      Bool

    externalCandidateEvidencePromotedIsFalse :
      externalCandidateEvidencePromoted ≡ false

    vacuumStateLabel :
      String

    vacuumStateLabelIsCanonical :
      vacuumStateLabel ≡ "Omega-vacuum-state"

    hamiltonianLabel :
      String

    hamiltonianLabelIsCanonical :
      hamiltonianLabel ≡ "H-vacuum-subtracted-Hamiltonian"

    spectrumPredicateLabel :
      String

    spectrumPredicateLabelIsCanonical :
      spectrumPredicateLabel ≡ "Spec(H) = {0} cup [Delta, infinity)"

    gapTargetLabel :
      String

    gapTargetLabelIsCanonical :
      gapTargetLabel ≡ "Delta > 0"

    massGapTargetRecorded :
      Bool

    massGapTargetRecordedIsTrue :
      massGapTargetRecorded ≡ true

    massGapPromoted :
      Bool

    massGapPromotedIsFalse :
      massGapPromoted ≡ false

    openObligations :
      List YangMillsMassGapOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYangMillsMassGapOpenObligations

    stoneHamiltonianGapBlockers :
      List YangMillsStoneHamiltonianGapOpenBlocker

    stoneHamiltonianGapBlockersAreCanonical :
      stoneHamiltonianGapBlockers
      ≡
      canonicalYangMillsStoneHamiltonianGapOpenBlockers

    physicalStoneGeneratorEqualsYMHamiltonianTargetRecorded :
      Bool

    physicalStoneGeneratorEqualsYMHamiltonianTargetRecordedIsTrue :
      physicalStoneGeneratorEqualsYMHamiltonianTargetRecorded ≡ true

    physicalStoneGeneratorEqualsYMHamiltonianPromoted :
      Bool

    physicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse :
      physicalStoneGeneratorEqualsYMHamiltonianPromoted ≡ false

    physicalStoneSpectralLowerBoundPromoted :
      Bool

    physicalStoneSpectralLowerBoundPromotedIsFalse :
      physicalStoneSpectralLowerBoundPromoted ≡ false

    proofShape :
      List String

    boundaryNotes :
      List String

open YangMillsMassGapBoundaryReceipt public

canonicalYangMillsMassGapBoundaryReceipt :
  YangMillsMassGapBoundaryReceipt
canonicalYangMillsMassGapBoundaryReceipt =
  record
    { upstreamMassGapReceipt =
        YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; ymConstructive5DExternalCandidate =
        YM5D.canonicalYMConstructive5DProofReceipt
    ; gribovResolutionExternalCandidate =
        Gribov.canonicalGribovResolutionAuthorityReceipt
    ; topologicalMassGapExternalCandidate =
        Topological.canonicalTopologicalMassGapInterpretationReceipt
    ; externalCandidateEvidencePromoted =
        false
    ; externalCandidateEvidencePromotedIsFalse =
        refl
    ; vacuumStateLabel =
        "Omega-vacuum-state"
    ; vacuumStateLabelIsCanonical =
        refl
    ; hamiltonianLabel =
        "H-vacuum-subtracted-Hamiltonian"
    ; hamiltonianLabelIsCanonical =
        refl
    ; spectrumPredicateLabel =
        "Spec(H) = {0} cup [Delta, infinity)"
    ; spectrumPredicateLabelIsCanonical =
        refl
    ; gapTargetLabel =
        "Delta > 0"
    ; gapTargetLabelIsCanonical =
        refl
    ; massGapTargetRecorded =
        true
    ; massGapTargetRecordedIsTrue =
        refl
    ; massGapPromoted =
        false
    ; massGapPromotedIsFalse =
        refl
    ; openObligations =
        canonicalYangMillsMassGapOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; stoneHamiltonianGapBlockers =
        canonicalYangMillsStoneHamiltonianGapOpenBlockers
    ; stoneHamiltonianGapBlockersAreCanonical =
        refl
    ; physicalStoneGeneratorEqualsYMHamiltonianTargetRecorded =
        true
    ; physicalStoneGeneratorEqualsYMHamiltonianTargetRecordedIsTrue =
        refl
    ; physicalStoneGeneratorEqualsYMHamiltonianPromoted =
        false
    ; physicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse =
        refl
    ; physicalStoneSpectralLowerBoundPromoted =
        false
    ; physicalStoneSpectralLowerBoundPromotedIsFalse =
        refl
    ; proofShape =
        "finite-volume coercivity"
        ∷ "reflection positivity"
        ∷ "transfer-matrix positivity"
        ∷ "spectral-projection isolation"
        ∷ "continuum-limit stability"
        ∷ "infinite-volume stability"
        ∷ []
    ; boundaryNotes =
        "The finite-depth mass-gap receipt is reused as the upstream anchor"
        ∷ "A withdrawn 5D constructive YM route, Cambridge Engage Agawa, and Zenodo 19423313 are recorded as non-promoting external candidate receipts"
        ∷ "The continuum Clay theorem remains outside this boundary module"
        ∷ "The spectral gap is recorded as the target shape, not a terminal promotion"
        ∷ "Physical Stone generator = Yang-Mills Hamiltonian is recorded only as a target"
        ∷ "The selected-carrier lower bound is not promoted as a physical Stone spectral lower bound"
        ∷ []
    }

yangMillsMassGapFirstOpenObligation :
  YangMillsMassGapOpenObligation
yangMillsMassGapFirstOpenObligation =
  missingFiniteVolumeCoercivity
