module DASHI.Culture.ElliottMillerPluralLensWrongTypeHumourCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact as Elliott
import DASHI.Culture.AliceMillerChildhoodAuthorityPluralLensExact as Miller
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snow
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge as Humour
import DASHI.Interop.SensibLawOntologyTopology as Wrong

------------------------------------------------------------------------
-- SHARED REGRESSION: SURFACE != ROLE != AUTHORITY != MEANING != OUTCOME
------------------------------------------------------------------------

data SurfaceRoleAxis : Set where
  visibleCategory : SurfaceRoleAxis
  imposedMeaning : SurfaceRoleAxis
  speakerOrInstitutionAuthority : SurfaceRoleAxis
  participantAssent : SurfaceRoleAxis
  historicalContext : SurfaceRoleAxis
  humourIronyRegister : SurfaceRoleAxis
  downstreamEffect : SurfaceRoleAxis
  sourceProvenance : SurfaceRoleAxis

data DemoState : Set where literalUse ironicUse : DemoState
data DemoSurface : Set where sameWords : DemoSurface
data DemoMeaning : Set where literalMeaning ironicMeaning : DemoMeaning

surface : DemoState → DemoSurface
surface state = sameWords

meaning : DemoState → DemoMeaning
meaning literalUse = literalMeaning
meaning ironicUse = ironicMeaning

surfaceCannotRecoverRegister : INF.FactorsThrough surface meaning → ⊥
surfaceCannotRecoverRegister factors =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness literalUse ironicUse refl (λ ()))
    factors

record CrossPollinationReading : Set where
  constructor cross-pollination-reading
  field
    elliottShowsAuthorityCanLoadArbitraryClassifier : Bool
    millerShowsAuthorityCanConstrainChildVoice : Bool
    humourShowsSameSurfaceMayCarryDifferentRegister : Bool
    wrongTypeBlocksSurfaceRoleSubstitution : Bool
    fallacyAuditBlocksUnsupportedPromotion : Bool
    factorsThroughTestsConsumerSufficiency : Bool
    failedFactorisationCanSnowballAxis : Bool
open CrossPollinationReading public

canonicalCrossPollinationReading : CrossPollinationReading
canonicalCrossPollinationReading = cross-pollination-reading
  true true true true true true true

record DiagnosticRoute : Set where
  constructor diagnostic-route
  field
    discoveryRoute : Snow.DiscoveryRoute
    reading : String
    automaticTruthPromotion : Bool
open DiagnosticRoute public

wrongTypeRoute : DiagnosticRoute
wrongTypeRoute = diagnostic-route Snow.wrongTypeDiagnosis
  "candidate has the wrong semantic/legal/epistemic type for the requested downstream role"
  false

fallacyRoute : DiagnosticRoute
fallacyRoute = diagnostic-route Snow.fallacyDiagnosis
  "inference attempts unsupported promotion such as possible->necessary, label->essence, or evidence->authority"
  false

humourRoute : DiagnosticRoute
humourRoute = diagnostic-route Snow.humourRepresentationMismatch
  "surface representation underdetermines pragmatic register, speaker stance and downstream meaning"
  false

experimentalRoute : DiagnosticRoute
experimentalRoute = diagnostic-route Snow.experimentalDesign
  "design a discriminator for the unresolved coordinate rather than infer it from the coarse surface"
  false

data SameLabelCreatesSameRole : Set where
data AuthorityAssertionCreatesFact : Set where
data HumourDecodingCreatesSpeakerIntent : Set where
data FallacyNameProvesFalsehood : Set where
data WrongTypeNameProvesViolation : Set where

sameLabelDoesNotCreateSameRole : SameLabelCreatesSameRole → ⊥
sameLabelDoesNotCreateSameRole ()
authorityAssertionDoesNotCreateFact : AuthorityAssertionCreatesFact → ⊥
authorityAssertionDoesNotCreateFact ()
humourDecodingDoesNotCreateIntent : HumourDecodingCreatesSpeakerIntent → ⊥
humourDecodingDoesNotCreateIntent ()
fallacyNameDoesNotProveFalsehood : FallacyNameProvesFalsehood → ⊥
fallacyNameDoesNotProveFalsehood ()
wrongTypeNameDoesNotProveViolation : WrongTypeNameProvesViolation → ⊥
wrongTypeNameDoesNotProveViolation ()
