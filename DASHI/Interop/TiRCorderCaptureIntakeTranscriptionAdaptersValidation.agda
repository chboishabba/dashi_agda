module DASHI.Interop.TiRCorderCaptureIntakeTranscriptionAdaptersValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (zero)

import DASHI.Interop.TiRCorderCaptureIntakeTranscriptionAdaptersExact as Adapter
import DASHI.Interop.TiRCorderSensiBlawConnectorBoundary as Boundary

captureFixture : Adapter.CaptureInput
captureFixture =
  Adapter.captureInput
    "device-1"
    "session-1"
    "capture.wav"
    "audio-sha256"
    "2026-10-28T00:00:00Z"
    "2026-10-28T00:01:00Z"

transcriptFixture : Adapter.TranscriptInput
transcriptFixture =
  Adapter.transcriptInput
    "utt-1"
    "2026-10-28T00:00:00Z"
    "2026-10-28T00:00:01Z"
    "speaker-1"
    zero
    "hello"
    []
    []
    zero
    zero
    zero

intakeFixture : Adapter.IntakeInput
intakeFixture =
  Adapter.intakeInput
    captureFixture
    "transcript-sha256"
    (transcriptFixture ∷ [])
    []
    "raw-payload-1"

batchFixture : Adapter.BatchInput
batchFixture =
  Adapter.batchInput
    "batch-1"
    "2026-10-28T00:02:00Z"
    "cursor-0"
    "cursor-1"
    (intakeFixture ∷ [])

_ :
  Boundary.CaptureProvenance.deviceId
    (Adapter.captureAdapter captureFixture "transcript-sha256")
  ≡ "device-1"
_ = refl

_ :
  Boundary.CaptureProvenance.audioHash
    (Adapter.captureAdapter captureFixture "transcript-sha256")
  ≡ "audio-sha256"
_ = refl

_ :
  Boundary.CaptureProvenance.transcriptHash
    (Adapter.captureAdapter captureFixture "transcript-sha256")
  ≡ "transcript-sha256"
_ = refl

_ :
  Boundary.UtteranceFrame.transcriptText
    (Adapter.transcriptionAdapter transcriptFixture)
  ≡ "hello"
_ = refl

_ :
  Boundary.TiRCSessionPacket.rawPayloadReference
    (Adapter.intakeAdapter intakeFixture)
  ≡ "raw-payload-1"
_ = refl

_ :
  Boundary.NormalizedTiRCBatch.batchId
    (Adapter.batchAdapter batchFixture)
  ≡ "batch-1"
_ = refl

_ :
  Boundary.NormalizedTiRCBatch.cursor
    (Adapter.batchAdapter batchFixture)
  ≡ "cursor-0"
_ = refl

_ :
  Boundary.NormalizedTiRCBatch.nextCursor
    (Adapter.batchAdapter batchFixture)
  ≡ "cursor-1"
_ = refl
