{-# OPTIONS --safe #-}
module DASHI.Culture.CriticalArtTemporalReceptionReuseExact where

------------------------------------------------------------------------
-- Source / ownership discipline
--
-- This is a DASHI APPLICATION of existing reception, residual, trace,
-- revision and trialectic owners, not a newly invented temporality.
-- Formal film theory by Peirce, Barthes, Mulvey, Metz, Bordwell, Smith,
-- Sobchack and others requires separate original-passage receipts.
-- No claim about a real spectator's mental state or the director's
-- intention follows from this structural adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact as Fibre
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Path
import DASHI.Reasoning.TrialecticThreeStrandBraidHistoryExact as Braid
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

-- The evidence owner and selected edition/scene must be paid separately.
-- The time-indexed fibre is the ORIGINAL installed owner; this record only
-- locates a possible artwork-specific consumer against that exact fibre.
record SourceIndexedArtReception : Set where
  constructor sourceIndexedArtReception
  field
    workIdentifier : String
    editionIdentifier : String
    sceneIdentifier : String
    originalEvidenceOwner : String
    history : Temporal.TemporalReceptionHistory
    observationTime : Temporal.ReceptionTime
    receptionFibre : Fibre.HistoryTimeIndexedReceptionFibre
    fibreSameOwner :
      receptionFibre ≡ Fibre.fibreAt history observationTime

-- Distinct channels, not a psychological diagnosis or value judgment.
data ArtEvidenceChannel : Set where
  characterConduct : ArtEvidenceChannel
  cinematicConstruction : ArtEvidenceChannel
  spectatorTestimony : ArtEvidenceChannel
  theoristInterpretation : ArtEvidenceChannel

characterIsNotCamera :
  characterConduct ≡ cinematicConstruction → ⊥
characterIsNotCamera ()

cameraIsNotMeasuredSpectator :
  cinematicConstruction ≡ spectatorTestimony → ⊥
cameraIsNotMeasuredSpectator ()

theoristIsNotSpectator :
  theoristInterpretation ≡ spectatorTestimony → ⊥
theoristIsNotSpectator ()

-- Existing temporal reception theorem: equality of time, present and
-- future projection cannot recover the finer history-bearing fibre.
samePresentFutureCannotRecoverFineReception :
  NF.FactorsThrough
    Fibre.sameTimePresentFuture
    Fibre.fineFibreCode → ⊥
samePresentFutureCannotRecoverFineReception =
  Fibre.sameTimePresentFutureCannotRecoverFineFibre

-- Existing braid history theorem: the attached triadic face need not
-- reconstruct the retained process route, even across an admitted
-- Yang--Baxter process equivalence.
sameFaceCannotRecoverRetainedBraidRoute :
  Descent.FactorsThrough Braid.faceOf Braid.routeOf → ⊥
sameFaceCannotRecoverRetainedBraidRoute =
  Braid.braidRouteDoesNotFactorThroughAttachedFace

-- Existing append-only proof: later evidence changes the selected
-- conclusion without deleting the earlier observation. This is a
-- canonical synthetic fixture, NOT a measured cinematic response.
priorSupportPersistsAfterDefeater :
  Revision.FixtureContains Revision.supportObservation
    (Revision.appendFixture Revision.supportOnly
      Revision.defeaterObservation)
priorSupportPersistsAfterDefeater =
  Revision.supportPersistsAfterDefeater

-- Film source/edition data remain external: only an explicitly selected
-- source-indexed instantiation of the existing temporal fibre is admitted.
syntheticEditionFixture : SourceIndexedArtReception
syntheticEditionFixture =
  sourceIndexedArtReception
    "SYNTHETIC ONLY: no film verification"
    "fixture edition"
    "fixture scene"
    "DASHI temporal reception formal test"
    Temporal.movementEarlyAuthorityHistory
    Temporal.t1
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
    refl

-- A scene's character channel never itself supplies evidence of
-- measured audience reception or original authorial endorsement.
data SceneDepictionCertifiesAuthorialEndorsement : Set where
data FormalFramingCertifiesMeasuredAudienceEffect : Set where
data LiteraryCritiqueIdentifiesHostileOperation : Set where

noAuthorshipPromotion :
  SceneDepictionCertifiesAuthorialEndorsement → ⊥
noAuthorshipPromotion ()

noAudienceEffectPromotion :
  FormalFramingCertifiesMeasuredAudienceEffect → ⊥
noAudienceEffectPromotion ()

noWarfarePromotion :
  LiteraryCritiqueIdentifiesHostileOperation → ⊥
noWarfarePromotion ()
