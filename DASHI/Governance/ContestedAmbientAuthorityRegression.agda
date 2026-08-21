module DASHI.Governance.ContestedAmbientAuthorityRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Interop.InspectionRelativeNoTypedMeet as NoMeet
import DASHI.Interop.PNFHyperfabric369 as Hyperfabric

------------------------------------------------------------------------
-- Focused regression for the contested-ambient convergence layer.
------------------------------------------------------------------------

partialInterfaceStillHasIndependentExterior :
  Ambient.ExteriorWitness Ambient.canonicalPartialInterface
partialInterfaceStillHasIndependentExterior = Ambient.canonicalExterior

independentlyAuthoritativeExteriorStillExists :
  Ambient.IndependentlyAuthoritativeExterior Ambient.canonicalPartialInterface
independentlyAuthoritativeExteriorStillExists = Ambient.canonicalIndependentExterior

partialInterfaceStillCannotBecomeSourceExhaustive :
  Ambient.LeftExhaustive Ambient.canonicalPartialInterface → ⊥
partialInterfaceStillCannotBecomeSourceExhaustive =
  Ambient.recognitionInterfaceDoesNotExhaustSourceCarrier

sourceAmbientClaimStillHasIndependentAdmissibleSource :
  Ambient.LegitimateAmbientAuthority Ambient.sourceAmbientClaim
sourceAmbientClaimStillHasIndependentAdmissibleSource =
  Ambient.sourceAmbientClaimHasAdmissibleSource

forceDominantAmbientClaimStillCannotSelfLegitimate :
  Ambient.LegitimateAmbientAuthority Ambient.forceDominantAmbientClaim →
  Authority.Never
forceDominantAmbientClaimStillCannotSelfLegitimate =
  Ambient.coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority

externalRecognitionStillCannotSelfIssueAuthority :
  Authority.AdmissibleAuthoritySource Authority.externalRecognitionAlone →
  Authority.Never
externalRecognitionStillCannotSelfIssueAuthority =
  Ambient.recognitionAloneDoesNotCreateAmbientAuthority

currentNoTypedMeetStillDoesNotBecomeGlobalImpossibility :
  NoMeet.GlobalNoTypedMeetClaim.globalImpossibilityPromoted
    NoMeet.canonicalGlobalNoTypedMeetClaim
  ≡ false
currentNoTypedMeetStillDoesNotBecomeGlobalImpossibility =
  Ambient.noTypedMeetStillDoesNotPromoteGlobalImpossibility

currentNoTypedMeetStillLeavesExteriorStatePresent :
  NoMeet.NoTypedMeetAtInspection →
  Ambient.ExteriorWitness Ambient.canonicalPartialInterface
currentNoTypedMeetStillLeavesExteriorStatePresent =
  Ambient.canonicalExteriorSurvivesCurrentNoTypedMeet

shared369FabricStillDoesNotPromoteExternalTheorem :
  Hyperfabric.hyperfabricPromotesExternalTheorem
    Hyperfabric.universalMathLanguageHyperfabric
  ≡ false
shared369FabricStillDoesNotPromoteExternalTheorem =
  Ambient.sharedHyperformalCarrierDoesNotPromoteExternalTheorem
    Hyperfabric.universalMathLanguageHyperfabric

primitiveHostStillBlocked :
  Ambient.ContestedAmbientAuthorityBoundary.oneCarrierPrimitiveHost
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ false
primitiveHostStillBlocked = refl

sourceAnnihilationStillBlocked :
  Ambient.ContestedAmbientAuthorityBoundary.noTypedMeetAnnihilatesSourceState
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ false
sourceAnnihilationStillBlocked = refl

recognitionExhaustionStillBlocked :
  Ambient.ContestedAmbientAuthorityBoundary.interfaceRecognitionExhaustsSource
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ false
recognitionExhaustionStillBlocked = refl

coercionAuthorityPromotionStillBlocked :
  Ambient.ContestedAmbientAuthorityBoundary.coerciveDominanceCreatesLegitimateAuthority
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ false
coercionAuthorityPromotionStillBlocked = refl

independentExteriorStillExplicitlyAllowed :
  Ambient.ContestedAmbientAuthorityBoundary.independentlyAuthoritativeExteriorAllowed
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ true
independentExteriorStillExplicitlyAllowed = refl

ambientAuthorityStillClaimIndexed :
  Ambient.ContestedAmbientAuthorityBoundary.ambientAuthorityMustBeClaimIndexed
    Ambient.canonicalContestedAmbientAuthorityBoundary
  ≡ true
ambientAuthorityStillClaimIndexed = refl
