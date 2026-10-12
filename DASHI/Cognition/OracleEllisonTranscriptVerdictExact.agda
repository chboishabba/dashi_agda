module DASHI.Cognition.OracleEllisonTranscriptVerdictExact where

------------------------------------------------------------------------
-- TRANSCRIPT VERDICT SURFACE
--
-- Verdicts are claim-relative evidence states, not person-level credibility
-- scores. "Interpretive" means a hypothesis/reading has been identified but
-- the acquired sources do not pay it as an empirical fact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.OracleEllisonTranscriptClaimAtlasExact as Claims

data Verdict : Set where
  supported : Verdict
  partiallySupported : Verdict
  interpretiveUnpaid : Verdict
  unsupported : Verdict
  contradictedOrMateriallyCounterevidenced : Verdict

verdict : Claims.TranscriptClaim → Verdict
verdict Claims.netanyahuSayeretService = supported
verdict Claims.netanyahuSayeretControlWorldview = unsupported
verdict Claims.netanyahuPermanentThreatMaintenanceMotive = interpretiveUnpaid
verdict Claims.ellisonFIDFDonation = supported
verdict Claims.ellisonNetanyahuReportedRelationshipActivity = supported
verdict Claims.ellisonImmortalityMotive = unsupported
verdict Claims.oracleChinaPoliceGoldenShield = supported
verdict Claims.oracleRafaelDefenseIntegration = supported
verdict Claims.oracleDeclaredDefenseNationalSecurityOrientation = supported
verdict Claims.oracleNimbusPrimeCloudProvider = contradictedOrMateriallyCounterevidenced
verdict Claims.oracleWritesIsraeliSecurityBlueprint = unsupported
verdict Claims.commonControllerFromSharedVendor = unsupported

------------------------------------------------------------------------
-- Promotion semantics.
------------------------------------------------------------------------

verdictCreatesMotiveTruth : Verdict → Bool
verdictCreatesMotiveTruth _ = false

supportedMeansAllDownstreamInferencesSupported : Verdict → Bool
supportedMeansAllDownstreamInferencesSupported _ = false

interpretiveMeansFalse : Verdict → Bool
interpretiveMeansFalse _ = false

counterevidenceMeansNoOracleIsraelRelationship : Verdict → Bool
counterevidenceMeansNoOracleIsraelRelationship _ = false

unsupportedMeansContradicted : Verdict → Bool
unsupportedMeansContradicted _ = false

relationshipSupportCreatesPolicyControl : Verdict → Bool
relationshipSupportCreatesPolicyControl _ = false

defensePostureSupportCreatesSovereignControl : Verdict → Bool
defensePostureSupportCreatesSovereignControl _ = false

------------------------------------------------------------------------
-- Key regressions.
------------------------------------------------------------------------

serviceSupportedButWorldviewNot :
  verdict Claims.netanyahuSayeretService ≡ supported
serviceSupportedButWorldviewNot = refl

ellisonNetanyahuRelationshipSupported :
  verdict Claims.ellisonNetanyahuReportedRelationshipActivity ≡ supported
ellisonNetanyahuRelationshipSupported = refl

oracleChinaSupported :
  verdict Claims.oracleChinaPoliceGoldenShield ≡ supported
oracleChinaSupported = refl

oracleRafaelSupported :
  verdict Claims.oracleRafaelDefenseIntegration ≡ supported
oracleRafaelSupported = refl

oracleDefenseOrientationSupported :
  verdict Claims.oracleDeclaredDefenseNationalSecurityOrientation ≡ supported
oracleDefenseOrientationSupported = refl

oracleNimbusPrimeCounterevidenced :
  verdict Claims.oracleNimbusPrimeCloudProvider
  ≡ contradictedOrMateriallyCounterevidenced
oracleNimbusPrimeCounterevidenced = refl

oracleBlueprintUnsupportedNotRefuted :
  verdict Claims.oracleWritesIsraeliSecurityBlueprint
  ≡ unsupported
oracleBlueprintUnsupportedNotRefuted = refl

record VerdictBoundary : Set where
  constructor verdict-boundary
  field
    claimRelative : Bool
    sourceIdentityIsNotVerdict : Bool
    supportedAntecedentDoesNotPayConsequent : Bool
    motiveRequiresIndependentPayment : Bool
    counterevidenceCanBeLocalToOneClaim : Bool
    unsupportedDoesNotMeanFalse : Bool
    relationshipSupportDoesNotCreatePolicyControl : Bool
    defensePostureSupportDoesNotCreateSovereignControl : Bool

canonicalVerdictBoundary : VerdictBoundary
canonicalVerdictBoundary =
  verdict-boundary true true true true true true true true
