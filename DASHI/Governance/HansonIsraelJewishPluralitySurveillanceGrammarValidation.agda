module DASHI.Governance.HansonIsraelJewishPluralitySurveillanceGrammarValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonIsraelJewishPluralitySurveillanceGrammarExact as H

communitySafetyDoesNotDetermineUniversalRouting :
  INF.FactorsThrough H.communitySafetyObserver H.minorityRouting → ⊥
communitySafetyDoesNotDetermineUniversalRouting =
  H.communitySafetyVocabularyCannotDetermineUniversalProtection

jewishCommunityNotIsraelState :
  H.JewishCommunityEqualsIsraelState → ⊥
jewishCommunityNotIsraelState =
  H.jewishCommunityDoesNotEqualIsraelState

ajaNotAllAustralianJews :
  H.AJAEqualsAllAustralianJews → ⊥
ajaNotAllAustralianJews =
  H.ajaDoesNotEqualAllAustralianJews

aijacNotAllAustralianJews :
  H.AIJACEqualsAllAustralianJews → ⊥
aijacNotAllAustralianJews =
  H.aijacDoesNotEqualAllAustralianJews

israelSupportNotUniversalProtection :
  H.SupportForIsraelEqualsUniversalMinorityProtection → ⊥
israelSupportNotUniversalProtection =
  H.israelSupportDoesNotAutoPayUniversalMinorityProtection

noHansonSegalPalantirNetwork :
  H.HansonSegalPalantirCoordinatedNetworkEstablished → ⊥
noHansonSegalPalantirNetwork =
  H.noTriadicNetworkConstructed

publicAffairsNotPolicyCapture :
  H.PublicAffairsProvesPolicyCapture → ⊥
publicAffairsNotPolicyCapture =
  H.publicAffairsDoesNotProveCapture

palantirContractNotAbuse :
  H.GovernmentContractProvesAbuse → ⊥
palantirContractNotAbuse =
  H.contractDoesNotProveAbuse

palantirContractNotNeutrality :
  H.GovernmentContractProvesNeutrality → ⊥
palantirContractNotNeutrality =
  H.contractDoesNotProveNeutrality

triadicNetworkFlagFalse :
  H.hansonSegalPalantirNetworkConstructed
    H.canonicalHansonIsraelJewishSurveillanceBoundary
    ≡ false
triadicNetworkFlagFalse =
  H.hansonSegalPalantirNetworkConstructedIsFalse
    H.canonicalHansonIsraelJewishSurveillanceBoundary

policyCaptureFlagFalse :
  H.publicAffairsPolicyCaptureAutomaticallyProved
    H.canonicalHansonIsraelJewishSurveillanceBoundary
    ≡ false
policyCaptureFlagFalse =
  H.publicAffairsPolicyCaptureAutomaticallyProvedIsFalse
    H.canonicalHansonIsraelJewishSurveillanceBoundary

panopticonAuthorityFlagFalse :
  H.panopticonAuthorityConstructedFromCapability
    H.canonicalHansonIsraelJewishSurveillanceBoundary
    ≡ false
panopticonAuthorityFlagFalse =
  H.panopticonAuthorityConstructedFromCapabilityIsFalse
    H.canonicalHansonIsraelJewishSurveillanceBoundary
