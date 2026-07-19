module DASHI.Core.ReplayArtifactCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record ReplayArtifactCore : Set where
  constructor replayArtifactCore
  field
    artifactLabel       : String
    artifactLocator     : String
    validationCommand   : String
    replayable          : Bool
    replayPromotesTruth : Bool

open ReplayArtifactCore public

canonicalReplayArtifact : String → String → String → ReplayArtifactCore
canonicalReplayArtifact label locator command =
  replayArtifactCore label locator command true false

canonicalReplayIsReplayable :
  (label locator command : String) →
  replayable (canonicalReplayArtifact label locator command) ≡ true
canonicalReplayIsReplayable label locator command = refl

canonicalReplayDoesNotPromoteTruth :
  (label locator command : String) →
  replayPromotesTruth (canonicalReplayArtifact label locator command) ≡ false
canonicalReplayDoesNotPromoteTruth label locator command = refl
