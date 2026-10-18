module DASHI.Education.DigitalESDEmpiricalAuthorityFirewallRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEmpiricalAuthorityFirewallExact as Firewall

formalEntailmentNotGroundingRegression :
  Firewall.FormalEntailmentDeterminesEmpiricalGrounding → ⊥
formalEntailmentNotGroundingRegression =
  Firewall.formalEntailmentDoesNotDetermineEmpiricalGrounding

reproducibilityNotCorrectnessRegression :
  Firewall.ProceduralReproducibilityDeterminesExtractionCorrectness → ⊥
reproducibilityNotCorrectnessRegression =
  Firewall.proceduralReproducibilityDoesNotDetermineExtractionCorrectness

attributionNotSupportRegression :
  Firewall.AttributionCompletenessDeterminesClaimSupport → ⊥
attributionNotSupportRegression =
  Firewall.attributionCompletenessDoesNotDetermineClaimSupport

hashNotTruthRegression :
  Firewall.ContentHashDeterminesClaimTruth → ⊥
hashNotTruthRegression = Firewall.contentHashDoesNotDetermineClaimTruth

boundaryRetainedRegression :
  Firewall.EmpiricalAuthorityBoundary.formalProcessingCreatesEmpiricalAuthority
    Firewall.canonicalEmpiricalAuthorityBoundary
  ≡ false
boundaryRetainedRegression = refl

claimCeilingRetainedRegression :
  Firewall.EmpiricalAuthorityBoundary.claimCeilingRemainsIndependent
    Firewall.canonicalEmpiricalAuthorityBoundary
  ≡ true
claimCeilingRetainedRegression = refl
