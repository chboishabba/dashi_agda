module DASHI.Reasoning.PlatoSymposiumTransmissionAttributionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Reasoning.PlatoSymposiumTransmissionAttributionExact as Bridge

immediateSpeakerDoesNotFixClaimRole :
  Query.FactorsThrough
    Bridge.claimRoleQuestions
    Bridge.immediateSpeakerProjection
    Bridge.claimRoleQuestion → ⊥
immediateSpeakerDoesNotFixClaimRole =
  Bridge.immediateSpeakerDoesNotDetermineClaimRole

reportedSourceIsNotImmediateSpeakerByBoundary :
  Bridge.immediateSpeakerEqualsReportedSource
    Bridge.canonicalPlatoSymposiumTransmissionBoundary ≡ false
reportedSourceIsNotImmediateSpeakerByBoundary = refl

formalisationAuthorIsNotDialogueAuthor :
  Bridge.dialogueAuthorEqualsFormalisationAuthor
    Bridge.canonicalPlatoSymposiumTransmissionBoundary ≡ false
formalisationAuthorIsNotDialogueAuthor = refl

transmissionDoesNotCreateProofAuthority :
  Bridge.transmissionPathCreatesProofAuthority
    Bridge.canonicalPlatoSymposiumTransmissionBoundary ≡ false
transmissionDoesNotCreateProofAuthority = refl

jmdAttributionIsRetained :
  Bridge.JMDAttributionRetained
    Bridge.canonicalPlatoSymposiumTransmissionBoundary ≡ true
jmdAttributionIsRetained = refl

sourceRoleSurvivesSnowball :
  Bridge.sourceRoleRetainedAcrossSnowball
    Bridge.canonicalPlatoSymposiumTransmissionBoundary ≡ true
sourceRoleSurvivesSnowball = refl
