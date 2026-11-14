module DASHI.WorldModel.VERIDLegacyExperimentProjectionReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Programmes.ResearchProgrammeExact as Programme
import DASHI.Programmes.TestHarnessExact as TestHarness
import DASHI.Programmes.DashifineExact as Dashifine
import DASHI.Programmes.DashifineWaveProjectionFamilyExact as Projection
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.WorldModel.VERIDExperimentProofSearchBridgeExact as VERID

------------------------------------------------------------------------
-- Legacy programme reuse is by programme contract, not script duplication.
-- The finite projection regression illustrates loss of a safety-relevant
-- coordinate. A physical bound still needs an empirical contact receipt.
------------------------------------------------------------------------

legacyTestProgramme : Programme.ResearchProgramme
legacyTestProgramme = TestHarness.dashitestProgramme

legacyFineProgramme : Programme.ResearchProgramme
legacyFineProgramme = Dashifine.dashifineProgramme

fullObserver : Bool → Bool
fullObserver b = b

projectedObserver : Bool → Bool
projectedObserver _ = false

projectedCollides : projectedObserver false ≡ projectedObserver true
projectedCollides = refl

fullSeparates : fullObserver false ≡ fullObserver true → ⊥
fullSeparates ()

projectedCollision : Discriminator.CurrentObserverCollision projectedObserver
projectedCollision =
  Discriminator.currentObserverCollision false true projectedCollides

fullMeasurement : Discriminator.ExperimentBundle Bool
fullMeasurement =
  Discriminator.experimentBundle Bool fullObserver 1
    "finite projection stress test: retain discriminating coordinate"
    "symbolic fixture only; instrument calibration unpaid"

projectionRepair : Discriminator.DiscriminatingLanguageExtension projectedObserver
projectionRepair =
  Discriminator.discriminatingLanguageExtension
    projectedCollision fullMeasurement
    (Discriminator.bundleSeparates fullSeparates)

repairedJointObservationSeparates :
  Discriminator.joinedObservation projectedObserver fullMeasurement false
  ≡ Discriminator.joinedObservation projectedObserver fullMeasurement true → ⊥
repairedJointObservationSeparates =
  Discriminator.extensionJoinSeparates projectionRepair

-- Modelled results under one projection cannot pay all projection-task
-- receipts. Preserve the canonical programme's declared stress boundary.
projectionBenchmarkBoundary : Projection.DashifineWaveProjectionBoundary
projectionBenchmarkBoundary = Projection.canonicalDashifineWaveProjectionBoundary

predictionEnvelopeBoundary : Envelope.PredictionEnvelopeBoundary
predictionEnvelopeBoundary = Envelope.canonicalPredictionEnvelopeBoundary
