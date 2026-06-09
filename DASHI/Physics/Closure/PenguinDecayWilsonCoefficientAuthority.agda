module DASHI.Physics.Closure.PenguinDecayWilsonCoefficientAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Penguin
import DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority as Baseline

------------------------------------------------------------------------
-- Versioned Wilson-coefficient authority for the penguin empirical lane.
--
-- This module binds the Standard-Model b -> s mu+ mu- baseline request to a
-- versioned flavio/EOS-style authority surface.  It records the C10/Wilson
-- and theory-uncertainty obligations that must travel with any later
-- comparison.  The canonical value is a concrete receipt, but it remains
-- fail-closed: no accepted token, empirical comparison, anomaly claim, or
-- promotion is constructed here.

data WilsonAuthorityStatus : Set where
  versionedExternalAuthorityNamedFreezeStillRequired :
    WilsonAuthorityStatus

data WilsonAuthorityProvider : Set where
  flavio :
    WilsonAuthorityProvider
  eos :
    WilsonAuthorityProvider

canonicalWilsonAuthorityProvider :
  WilsonAuthorityProvider
canonicalWilsonAuthorityProvider =
  flavio

data WilsonCoefficientRole : Set where
  C9SM :
    WilsonCoefficientRole
  C10SM :
    WilsonCoefficientRole
  C7EffSM :
    WilsonCoefficientRole
  C8EffSM :
    WilsonCoefficientRole

canonicalWilsonCoefficientRoles :
  List WilsonCoefficientRole
canonicalWilsonCoefficientRoles =
  C9SM
  ∷ C10SM
  ∷ C7EffSM
  ∷ C8EffSM
  ∷ []

data WilsonAuthorityField : Set where
  providerNameField :
    WilsonAuthorityField
  providerVersionField :
    WilsonAuthorityField
  documentationURLField :
    WilsonAuthorityField
  apiModuleURLField :
    WilsonAuthorityField
  observableKeyField :
    WilsonAuthorityField
  coefficientKeySetField :
    WilsonAuthorityField
  effectiveHamiltonianConventionField :
    WilsonAuthorityField
  renormalizationScaleField :
    WilsonAuthorityField
  smBranchingFractionField :
    WilsonAuthorityField
  theoryUncertaintyField :
    WilsonAuthorityField
  packageArtifactDigestField :
    WilsonAuthorityField
  environmentDigestField :
    WilsonAuthorityField
  noManualFitAttestationField :
    WilsonAuthorityField

canonicalWilsonAuthorityFields :
  List WilsonAuthorityField
canonicalWilsonAuthorityFields =
  providerNameField
  ∷ providerVersionField
  ∷ documentationURLField
  ∷ apiModuleURLField
  ∷ observableKeyField
  ∷ coefficientKeySetField
  ∷ effectiveHamiltonianConventionField
  ∷ renormalizationScaleField
  ∷ smBranchingFractionField
  ∷ theoryUncertaintyField
  ∷ packageArtifactDigestField
  ∷ environmentDigestField
  ∷ noManualFitAttestationField
  ∷ []

data C10WilsonObligation : Set where
  c10SMValue :
    C10WilsonObligation
  c10SignConvention :
    C10WilsonObligation
  c10EffectiveHamiltonianNormalization :
    C10WilsonObligation
  c10RenormalizationScale :
    C10WilsonObligation
  c10WilsonBasis :
    C10WilsonObligation

canonicalC10WilsonObligations :
  List C10WilsonObligation
canonicalC10WilsonObligations =
  c10SMValue
  ∷ c10SignConvention
  ∷ c10EffectiveHamiltonianNormalization
  ∷ c10RenormalizationScale
  ∷ c10WilsonBasis
  ∷ []

data C9C10WilsonDigestMissingAuthority : Set where
  missingC9SMNumericalValueAuthority :
    C9C10WilsonDigestMissingAuthority
  missingC10SMNumericalValueAuthority :
    C9C10WilsonDigestMissingAuthority
  missingC9C10SignAndBasisAuthority :
    C9C10WilsonDigestMissingAuthority
  missingC9C10ScaleAndHamiltonianAuthority :
    C9C10WilsonDigestMissingAuthority
  missingC9C10AuthorityDigest :
    C9C10WilsonDigestMissingAuthority

canonicalC9C10WilsonDigestMissingAuthorities :
  List C9C10WilsonDigestMissingAuthority
canonicalC9C10WilsonDigestMissingAuthorities =
  missingC9SMNumericalValueAuthority
  ∷ missingC10SMNumericalValueAuthority
  ∷ missingC9C10SignAndBasisAuthority
  ∷ missingC9C10ScaleAndHamiltonianAuthority
  ∷ missingC9C10AuthorityDigest
  ∷ []

record C9C10WilsonAuthorityDigest : Set where
  constructor mkC9C10WilsonAuthorityDigest
  field
    coefficientSetLabel :
      String

    coefficientSetLabelIsCanonical :
      coefficientSetLabel ≡ "C9SM/C10SM b -> s mu+ mu- Wilson authority"

    c9Key :
      String

    c9KeyIsCanonical :
      c9Key ≡ "C9_bsll"

    c10Key :
      String

    c10KeyIsCanonical :
      c10Key ≡ "C10_bsll"

    digestAlgorithm :
      String

    digestAlgorithmIsSHA256 :
      digestAlgorithm ≡ "sha256"

    authorityDigest :
      String

    authorityDigestIsRequired :
      authorityDigest
      ≡
      "required: sha256 digest of accepted C9/C10 Wilson coefficient authority artifact"

    missingAuthorities :
      List C9C10WilsonDigestMissingAuthority

    missingAuthoritiesAreCanonical :
      missingAuthorities
      ≡
      canonicalC9C10WilsonDigestMissingAuthorities

open C9C10WilsonAuthorityDigest public

canonicalC9C10WilsonAuthorityDigest :
  C9C10WilsonAuthorityDigest
canonicalC9C10WilsonAuthorityDigest =
  mkC9C10WilsonAuthorityDigest
    "C9SM/C10SM b -> s mu+ mu- Wilson authority"
    refl
    "C9_bsll"
    refl
    "C10_bsll"
    refl
    "sha256"
    refl
    "required: sha256 digest of accepted C9/C10 Wilson coefficient authority artifact"
    refl
    canonicalC9C10WilsonDigestMissingAuthorities
    refl

data TheoryUncertaintyComponent : Set where
  parametricInputUncertainty :
    TheoryUncertaintyComponent
  formFactorUncertainty :
    TheoryUncertaintyComponent
  perturbativeScaleUncertainty :
    TheoryUncertaintyComponent
  nonlocalCharmUncertainty :
    TheoryUncertaintyComponent
  covariancePropagationUncertainty :
    TheoryUncertaintyComponent

canonicalTheoryUncertaintyComponents :
  List TheoryUncertaintyComponent
canonicalTheoryUncertaintyComponents =
  parametricInputUncertainty
  ∷ formFactorUncertainty
  ∷ perturbativeScaleUncertainty
  ∷ nonlocalCharmUncertainty
  ∷ covariancePropagationUncertainty
  ∷ []

data P5PrimeAuthorityChainComponent : Set where
  p5PrimeAngularObservableComponent :
    P5PrimeAuthorityChainComponent
  c9WilsonCoefficientComponent :
    P5PrimeAuthorityChainComponent
  c10WilsonCoefficientComponent :
    P5PrimeAuthorityChainComponent
  formFactorAuthorityComponent :
    P5PrimeAuthorityChainComponent
  theoryUncertaintyAuthorityComponent :
    P5PrimeAuthorityChainComponent
  charmingPenguinSystematicComponent :
    P5PrimeAuthorityChainComponent

canonicalP5PrimeAuthorityChainComponents :
  List P5PrimeAuthorityChainComponent
canonicalP5PrimeAuthorityChainComponents =
  p5PrimeAngularObservableComponent
  ∷ c9WilsonCoefficientComponent
  ∷ c10WilsonCoefficientComponent
  ∷ formFactorAuthorityComponent
  ∷ theoryUncertaintyAuthorityComponent
  ∷ charmingPenguinSystematicComponent
  ∷ []

data P5PrimeAuthorityChainBlocker : Set where
  missingAcceptedP5PrimeObservableKeyFreeze :
    P5PrimeAuthorityChainBlocker
  missingAcceptedC9C10WilsonAuthorityDigest :
    P5PrimeAuthorityChainBlocker
  missingAcceptedFormFactorAuthority :
    P5PrimeAuthorityChainBlocker
  missingAcceptedTheoryUncertaintyBudget :
    P5PrimeAuthorityChainBlocker
  missingAcceptedCharmingPenguinSystematic :
    P5PrimeAuthorityChainBlocker
  missingAcceptedC1C2CurrentCurrentOperatorAuthority :
    P5PrimeAuthorityChainBlocker

canonicalP5PrimeAuthorityChainBlockers :
  List P5PrimeAuthorityChainBlocker
canonicalP5PrimeAuthorityChainBlockers =
  missingAcceptedP5PrimeObservableKeyFreeze
  ∷ missingAcceptedC9C10WilsonAuthorityDigest
  ∷ missingAcceptedFormFactorAuthority
  ∷ missingAcceptedTheoryUncertaintyBudget
  ∷ missingAcceptedCharmingPenguinSystematic
  ∷ missingAcceptedC1C2CurrentCurrentOperatorAuthority
  ∷ []

record P5PrimeFlavioWilsonAuthorityChain : Set where
  constructor mkP5PrimeFlavioWilsonAuthorityChain
  field
    p5PrimeAuthorityProvider :
      WilsonAuthorityProvider

    p5PrimeAuthorityProviderIsFlavio :
      p5PrimeAuthorityProvider ≡ flavio

    p5PrimeSMBaselineRequest :
      Baseline.SMBaselineAuthorityRequestDiagnostic

    p5PrimeSMBaselineRequestIsCanonical :
      p5PrimeSMBaselineRequest
      ≡
      Baseline.canonicalSMBaselineAuthorityRequestDiagnostic

    p5PrimeObservableKey :
      String

    p5PrimeObservableKeyIsRequired :
      p5PrimeObservableKey
      ≡
      "required: accepted flavio P5' angular observable key and bin map"

    chainComponents :
      List P5PrimeAuthorityChainComponent

    chainComponentsAreCanonical :
      chainComponents
      ≡
      canonicalP5PrimeAuthorityChainComponents

    c9WilsonRole :
      WilsonCoefficientRole

    c9WilsonRoleIsCanonical :
      c9WilsonRole ≡ C9SM

    c10WilsonRole :
      WilsonCoefficientRole

    c10WilsonRoleIsCanonical :
      c10WilsonRole ≡ C10SM

    c9C10AuthorityDigest :
      C9C10WilsonAuthorityDigest

    c9C10AuthorityDigestIsCanonical :
      c9C10AuthorityDigest
      ≡
      canonicalC9C10WilsonAuthorityDigest

    formFactorAuthorityPayloadField :
      Baseline.SMBaselineProviderPayloadField

    formFactorAuthorityPayloadFieldIsBaseline :
      formFactorAuthorityPayloadField
      ≡
      Baseline.formFactorSource

    theoryUncertaintyAuthorityField :
      Baseline.SMBaselineAuthorityField

    theoryUncertaintyAuthorityFieldIsBaseline :
      theoryUncertaintyAuthorityField
      ≡
      Baseline.theoryUncertaintyAuthority

    p5PrimeTheoryUncertaintyComponents :
      List TheoryUncertaintyComponent

    p5PrimeTheoryUncertaintyComponentsAreCanonical :
      p5PrimeTheoryUncertaintyComponents
      ≡
      canonicalTheoryUncertaintyComponents

    charmingPenguinAuthorityField :
      Baseline.SMBaselineAuthorityField

    charmingPenguinAuthorityFieldIsBaseline :
      charmingPenguinAuthorityField
      ≡
      Baseline.charmingPenguinAuthority

    charmingPenguinPayloadField :
      Baseline.SMBaselineProviderPayloadField

    charmingPenguinPayloadFieldIsBaseline :
      charmingPenguinPayloadField
      ≡
      Baseline.charmingPenguinModel

    experimentalSystematicsAuthorityField :
      Baseline.SMBaselineAuthorityField

    experimentalSystematicsAuthorityFieldIsBaseline :
      experimentalSystematicsAuthorityField
      ≡
      Baseline.systematicsAuthority

    c1C2CurrentCurrentAuthorityComplete :
      Bool

    c1C2CurrentCurrentAuthorityCompleteIsFalse :
      c1C2CurrentCurrentAuthorityComplete ≡ false

    chainBlockers :
      List P5PrimeAuthorityChainBlocker

    chainBlockersAreCanonical :
      chainBlockers
      ≡
      canonicalP5PrimeAuthorityChainBlockers

    p5PrimeAcceptedAuthorityTokenConstructedHere :
      Bool

    p5PrimeAcceptedAuthorityTokenConstructedHereIsFalse :
      p5PrimeAcceptedAuthorityTokenConstructedHere ≡ false

    p5PrimeAnomalyPromotionAuthorized :
      Bool

    p5PrimeAnomalyPromotionAuthorizedIsFalse :
      p5PrimeAnomalyPromotionAuthorized ≡ false

open P5PrimeFlavioWilsonAuthorityChain public

canonicalP5PrimeFlavioWilsonAuthorityChain :
  P5PrimeFlavioWilsonAuthorityChain
canonicalP5PrimeFlavioWilsonAuthorityChain =
  mkP5PrimeFlavioWilsonAuthorityChain
    flavio
    refl
    Baseline.canonicalSMBaselineAuthorityRequestDiagnostic
    refl
    "required: accepted flavio P5' angular observable key and bin map"
    refl
    canonicalP5PrimeAuthorityChainComponents
    refl
    C9SM
    refl
    C10SM
    refl
    canonicalC9C10WilsonAuthorityDigest
    refl
    Baseline.formFactorSource
    refl
    Baseline.theoryUncertaintyAuthority
    refl
    canonicalTheoryUncertaintyComponents
    refl
    Baseline.charmingPenguinAuthority
    refl
    Baseline.charmingPenguinModel
    refl
    Baseline.systematicsAuthority
    refl
    false
    refl
    canonicalP5PrimeAuthorityChainBlockers
    refl
    false
    refl
    false
    refl

data WilsonAuthorityMissingDigest : Set where
  missingProviderVersionDigest :
    WilsonAuthorityMissingDigest
  missingPackageArtifactDigest :
    WilsonAuthorityMissingDigest
  missingEnvironmentDigest :
    WilsonAuthorityMissingDigest
  missingDatasetDigest :
    WilsonAuthorityMissingDigest
  missingProjectionFreezeHash :
    WilsonAuthorityMissingDigest

canonicalWilsonAuthorityMissingDigests :
  List WilsonAuthorityMissingDigest
canonicalWilsonAuthorityMissingDigests =
  missingProviderVersionDigest
  ∷ missingPackageArtifactDigest
  ∷ missingEnvironmentDigest
  ∷ missingDatasetDigest
  ∷ missingProjectionFreezeHash
  ∷ []

record FlavioProviderVersionDigest : Set where
  constructor mkFlavioProviderVersionDigest
  field
    providerName :
      String

    providerNameIsFlavio :
      providerName ≡ "flavio"

    providerVersion :
      String

    providerVersionIsCanonical :
      providerVersion ≡ "2.7.0"

    digestAlgorithm :
      String

    digestAlgorithmIsSHA256 :
      digestAlgorithm ≡ "sha256"

    packageArtifactDigest :
      String

    packageArtifactDigestIsRequired :
      packageArtifactDigest
      ≡
      "required: provider-supplied flavio package artifact digest"

    environmentDigest :
      String

    environmentDigestIsRequired :
      environmentDigest
      ≡
      "required: provider-supplied flavio runtime environment digest"

    parameterCardDigest :
      String

    parameterCardDigestIsRequired :
      parameterCardDigest
      ≡
      "required: provider-supplied flavio parameter-card digest"

open FlavioProviderVersionDigest public

canonicalFlavioProviderVersionDigest :
  FlavioProviderVersionDigest
canonicalFlavioProviderVersionDigest =
  mkFlavioProviderVersionDigest
    "flavio"
    refl
    "2.7.0"
    refl
    "sha256"
    refl
    "required: provider-supplied flavio package artifact digest"
    refl
    "required: provider-supplied flavio runtime environment digest"
    refl
    "required: provider-supplied flavio parameter-card digest"
    refl

data FlavioAuthorityAPIEntryPoint : Set where
  flavioSMPredictionAPI :
    FlavioAuthorityAPIEntryPoint
  flavioSMUncertaintyAPI :
    FlavioAuthorityAPIEntryPoint
  flavioWilsonCoefficientModule :
    FlavioAuthorityAPIEntryPoint
  flavioEffectiveCoefficientExtraction :
    FlavioAuthorityAPIEntryPoint

canonicalFlavioAuthorityAPIEntryPoints :
  List FlavioAuthorityAPIEntryPoint
canonicalFlavioAuthorityAPIEntryPoints =
  flavioSMPredictionAPI
  ∷ flavioSMUncertaintyAPI
  ∷ flavioWilsonCoefficientModule
  ∷ flavioEffectiveCoefficientExtraction
  ∷ []

record FlavioConcreteAuthorityCandidate : Set where
  constructor mkFlavioConcreteAuthorityCandidate
  field
    providerVersionDigest :
      FlavioProviderVersionDigest

    providerVersionDigestIsCanonical :
      providerVersionDigest
      ≡
      canonicalFlavioProviderVersionDigest

    apiEntryPoints :
      List FlavioAuthorityAPIEntryPoint

    apiEntryPointsAreCanonical :
      apiEntryPoints ≡ canonicalFlavioAuthorityAPIEntryPoints

    smPredictionCall :
      String

    smPredictionCallIsCanonical :
      smPredictionCall ≡ "flavio.sm_prediction('BR(Bs->mumu)')"

    smUncertaintyCall :
      String

    smUncertaintyCallIsCanonical :
      smUncertaintyCall ≡ "flavio.sm_uncertainty('BR(Bs->mumu)')"

    wilsonCoefficientLabels :
      List String

    wilsonCoefficientLabelsAreCanonical :
      wilsonCoefficientLabels
      ≡
      ( "C9"
        ∷ "C10"
        ∷ "C9_bsll"
        ∷ "C10_bsll"
        ∷ [] )

    effectiveCoefficientExtractionDocumented :
      Bool

    effectiveCoefficientExtractionDocumentedIsTrue :
      effectiveCoefficientExtractionDocumented ≡ true

    packageEnvironmentAndParameterDigestsPresent :
      Bool

    packageEnvironmentAndParameterDigestsPresentIsFalse :
      packageEnvironmentAndParameterDigestsPresent ≡ false

open FlavioConcreteAuthorityCandidate public

canonicalFlavioConcreteAuthorityCandidate :
  FlavioConcreteAuthorityCandidate
canonicalFlavioConcreteAuthorityCandidate =
  mkFlavioConcreteAuthorityCandidate
    canonicalFlavioProviderVersionDigest
    refl
    canonicalFlavioAuthorityAPIEntryPoints
    refl
    "flavio.sm_prediction('BR(Bs->mumu)')"
    refl
    "flavio.sm_uncertainty('BR(Bs->mumu)')"
    refl
    ( "C9"
      ∷ "C10"
      ∷ "C9_bsll"
      ∷ "C10_bsll"
      ∷ [] )
    refl
    true
    refl
    false
    refl

data PromotionFailClosedBlocker : Set where
  noAcceptedWilsonAuthorityToken :
    PromotionFailClosedBlocker
  noSMBaselineAcceptedAuthorityToken :
    PromotionFailClosedBlocker
  noEmpiricalResidualComparison :
    PromotionFailClosedBlocker
  noAnomalyClaim :
    PromotionFailClosedBlocker
  noPhysicsPromotion :
    PromotionFailClosedBlocker

canonicalPromotionFailClosedBlockers :
  List PromotionFailClosedBlocker
canonicalPromotionFailClosedBlockers =
  noAcceptedWilsonAuthorityToken
  ∷ noSMBaselineAcceptedAuthorityToken
  ∷ noEmpiricalResidualComparison
  ∷ noAnomalyClaim
  ∷ noPhysicsPromotion
  ∷ []

data AcceptedWilsonCoefficientAuthorityToken : Set where

acceptedWilsonCoefficientAuthorityImpossibleHere :
  AcceptedWilsonCoefficientAuthorityToken →
  ⊥
acceptedWilsonCoefficientAuthorityImpossibleHere ()

record PenguinDecayWilsonCoefficientAuthority : Set where
  field
    status :
      WilsonAuthorityStatus

    provider :
      WilsonAuthorityProvider

    providerIsFlavio :
      provider ≡ flavio

    crossCheckProvider :
      WilsonAuthorityProvider

    crossCheckProviderIsEOS :
      crossCheckProvider ≡ eos

    providerNameText :
      String

    providerNameTextIsCanonical :
      providerNameText ≡ "flavio"

    providerDocumentationVersion :
      String

    providerDocumentationVersionIsCanonical :
      providerDocumentationVersion ≡ "2.7.0"

    flavioProviderVersionDigest :
      FlavioProviderVersionDigest

    flavioProviderVersionDigestIsCanonical :
      flavioProviderVersionDigest
      ≡
      canonicalFlavioProviderVersionDigest

    flavioConcreteAuthorityCandidate :
      FlavioConcreteAuthorityCandidate

    flavioConcreteAuthorityCandidateIsCanonical :
      flavioConcreteAuthorityCandidate
      ≡
      canonicalFlavioConcreteAuthorityCandidate

    documentationURL :
      String

    documentationURLIsCanonical :
      documentationURL ≡ "https://flav-io.github.io/docs/"

    smDocumentationURL :
      String

    smDocumentationURLIsCanonical :
      smDocumentationURL ≡ "https://flav-io.github.io/docs/sm.html"

    wilsonAPIModuleURL :
      String

    wilsonAPIModuleURLIsCanonical :
      wilsonAPIModuleURL
      ≡
      "https://flav-io.github.io/apidoc/flavio/physics/bdecays/wilsoncoefficients.m.html"

    observableContract :
      Contract.PenguinDecayObservableContract

    observableContractIsCanonical :
      observableContract ≡ Contract.canonicalPenguinDecayObservableContract

    smBaselineRequest :
      Baseline.SMBaselineAuthorityRequestDiagnostic

    smBaselineRequestIsCanonical :
      smBaselineRequest
      ≡
      Baseline.canonicalSMBaselineAuthorityRequestDiagnostic

    target :
      Baseline.SMBaselineComparisonTarget

    targetIsBToSMuMu :
      target ≡ Baseline.bToSMuPlusMuMinus

    decay :
      Penguin.RarePenguinDecay

    decayIsBToSLeptonPair :
      decay ≡ Penguin.bToSLeptonPair

    leptonPair :
      Baseline.TargetLeptonPair

    leptonPairIsMuPlusMuMinus :
      leptonPair ≡ Baseline.muPlusMuMinus

    observableKey :
      String

    observableKeyIsCanonical :
      observableKey ≡ "BR(Bs->mumu)"

    transitionKey :
      String

    transitionKeyIsCanonical :
      transitionKey ≡ "bs mumu"

    coefficientRoles :
      List WilsonCoefficientRole

    coefficientRolesAreCanonical :
      coefficientRoles ≡ canonicalWilsonCoefficientRoles

    coefficientKeyLabels :
      List String

    c10WilsonObligations :
      List C10WilsonObligation

    c10WilsonObligationsAreCanonical :
      c10WilsonObligations ≡ canonicalC10WilsonObligations

    c10WilsonObligationLabels :
      List String

    c9C10WilsonAuthorityDigest :
      C9C10WilsonAuthorityDigest

    c9C10WilsonAuthorityDigestIsCanonical :
      c9C10WilsonAuthorityDigest
      ≡
      canonicalC9C10WilsonAuthorityDigest

    authorityFields :
      List WilsonAuthorityField

    authorityFieldsAreCanonical :
      authorityFields ≡ canonicalWilsonAuthorityFields

    smCentralValue :
      String

    smCentralValueIsCanonical :
      smCentralValue ≡ "3.66"

    smCentralValueScale :
      String

    smCentralValueScaleIsCanonical :
      smCentralValueScale ≡ "1e-9"

    smTheoryUncertainty :
      String

    smTheoryUncertaintyIsCanonical :
      smTheoryUncertainty ≡ "0.14"

    theoryUncertaintyComponents :
      List TheoryUncertaintyComponent

    theoryUncertaintyComponentsAreCanonical :
      theoryUncertaintyComponents ≡ canonicalTheoryUncertaintyComponents

    theoryUncertaintyLabels :
      List String

    effectiveHamiltonianConvention :
      String

    renormalizationScaleBinding :
      String

    missingDigests :
      List WilsonAuthorityMissingDigest

    missingDigestsAreCanonical :
      missingDigests ≡ canonicalWilsonAuthorityMissingDigests

    acceptedAuthorityTokenConstructedHere :
      Bool

    acceptedAuthorityTokenConstructedHereIsFalse :
      acceptedAuthorityTokenConstructedHere ≡ false

    empiricalComparisonAuthorizedHere :
      Bool

    empiricalComparisonAuthorizedHereIsFalse :
      empiricalComparisonAuthorizedHere ≡ false

    anomalyClaimConstructedHere :
      Bool

    anomalyClaimConstructedHereIsFalse :
      anomalyClaimConstructedHere ≡ false

    promotionConstructedHere :
      Bool

    promotionConstructedHereIsFalse :
      promotionConstructedHere ≡ false

    failClosedBlockers :
      List PromotionFailClosedBlocker

    failClosedBlockersAreCanonical :
      failClosedBlockers ≡ canonicalPromotionFailClosedBlockers

    acceptedAuthorityTokenBlocked :
      AcceptedWilsonCoefficientAuthorityToken →
      ⊥

    smBaselineAcceptedAuthorityTokenBlocked :
      Baseline.SMBaselineAcceptedAuthorityToken →
      ⊥

    failClosedWitness :
      ⊤

    receiptSummary :
      List String

open PenguinDecayWilsonCoefficientAuthority public

canonicalPenguinDecayWilsonCoefficientAuthority :
  PenguinDecayWilsonCoefficientAuthority
canonicalPenguinDecayWilsonCoefficientAuthority =
  record
    { status =
        versionedExternalAuthorityNamedFreezeStillRequired
    ; provider =
        flavio
    ; providerIsFlavio =
        refl
    ; crossCheckProvider =
        eos
    ; crossCheckProviderIsEOS =
        refl
    ; providerNameText =
        "flavio"
    ; providerNameTextIsCanonical =
        refl
    ; providerDocumentationVersion =
        "2.7.0"
    ; providerDocumentationVersionIsCanonical =
        refl
    ; flavioProviderVersionDigest =
        canonicalFlavioProviderVersionDigest
    ; flavioProviderVersionDigestIsCanonical =
        refl
    ; flavioConcreteAuthorityCandidate =
        canonicalFlavioConcreteAuthorityCandidate
    ; flavioConcreteAuthorityCandidateIsCanonical =
        refl
    ; documentationURL =
        "https://flav-io.github.io/docs/"
    ; documentationURLIsCanonical =
        refl
    ; smDocumentationURL =
        "https://flav-io.github.io/docs/sm.html"
    ; smDocumentationURLIsCanonical =
        refl
    ; wilsonAPIModuleURL =
        "https://flav-io.github.io/apidoc/flavio/physics/bdecays/wilsoncoefficients.m.html"
    ; wilsonAPIModuleURLIsCanonical =
        refl
    ; observableContract =
        Contract.canonicalPenguinDecayObservableContract
    ; observableContractIsCanonical =
        refl
    ; smBaselineRequest =
        Baseline.canonicalSMBaselineAuthorityRequestDiagnostic
    ; smBaselineRequestIsCanonical =
        refl
    ; target =
        Baseline.bToSMuPlusMuMinus
    ; targetIsBToSMuMu =
        refl
    ; decay =
        Penguin.bToSLeptonPair
    ; decayIsBToSLeptonPair =
        refl
    ; leptonPair =
        Baseline.muPlusMuMinus
    ; leptonPairIsMuPlusMuMinus =
        refl
    ; observableKey =
        "BR(Bs->mumu)"
    ; observableKeyIsCanonical =
        refl
    ; transitionKey =
        "bs mumu"
    ; transitionKeyIsCanonical =
        refl
    ; coefficientRoles =
        canonicalWilsonCoefficientRoles
    ; coefficientRolesAreCanonical =
        refl
    ; coefficientKeyLabels =
        "C9_bsll"
        ∷ "C10_bsll"
        ∷ "C7eff_bs"
        ∷ "C8eff_bs"
        ∷ []
    ; c10WilsonObligations =
        canonicalC10WilsonObligations
    ; c10WilsonObligationsAreCanonical =
        refl
    ; c10WilsonObligationLabels =
        "C10_SM numerical value"
        ∷ "C10 sign convention"
        ∷ "effective Hamiltonian normalization"
        ∷ "renormalization scale"
        ∷ "Wilson basis"
        ∷ []
    ; c9C10WilsonAuthorityDigest =
        canonicalC9C10WilsonAuthorityDigest
    ; c9C10WilsonAuthorityDigestIsCanonical =
        refl
    ; authorityFields =
        canonicalWilsonAuthorityFields
    ; authorityFieldsAreCanonical =
        refl
    ; smCentralValue =
        "3.66"
    ; smCentralValueIsCanonical =
        refl
    ; smCentralValueScale =
        "1e-9"
    ; smCentralValueScaleIsCanonical =
        refl
    ; smTheoryUncertainty =
        "0.14"
    ; smTheoryUncertaintyIsCanonical =
        refl
    ; theoryUncertaintyComponents =
        canonicalTheoryUncertaintyComponents
    ; theoryUncertaintyComponentsAreCanonical =
        refl
    ; theoryUncertaintyLabels =
        "parametric input uncertainty"
        ∷ "form-factor uncertainty"
        ∷ "perturbative scale uncertainty"
        ∷ "nonlocal charm uncertainty"
        ∷ "covariance propagation uncertainty"
        ∷ []
    ; effectiveHamiltonianConvention =
        "DeltaB=1 effective Hamiltonian; C9 and C10 use flavio alpha_em/(4*pi) convention"
    ; renormalizationScaleBinding =
        "flavio default b-decay scale and parameter card must be digest-bound before comparison"
    ; missingDigests =
        canonicalWilsonAuthorityMissingDigests
    ; missingDigestsAreCanonical =
        refl
    ; acceptedAuthorityTokenConstructedHere =
        false
    ; acceptedAuthorityTokenConstructedHereIsFalse =
        refl
    ; empiricalComparisonAuthorizedHere =
        false
    ; empiricalComparisonAuthorizedHereIsFalse =
        refl
    ; anomalyClaimConstructedHere =
        false
    ; anomalyClaimConstructedHereIsFalse =
        refl
    ; promotionConstructedHere =
        false
    ; promotionConstructedHereIsFalse =
        refl
    ; failClosedBlockers =
        canonicalPromotionFailClosedBlockers
    ; failClosedBlockersAreCanonical =
        refl
    ; acceptedAuthorityTokenBlocked =
        acceptedWilsonCoefficientAuthorityImpossibleHere
    ; smBaselineAcceptedAuthorityTokenBlocked =
        Baseline.smBaselineAcceptedAuthorityTokenImpossibleHere
    ; failClosedWitness =
        tt
    ; receiptSummary =
        "B_s -> mu+ mu- is bound to the canonical b -> s mu+ mu- SM baseline request"
        ∷ "flavio is the primary versioned Wilson authority and EOS is recorded as the cross-check authority style"
        ∷ "flavio 2.7.0 SM APIs are recorded as flavio.sm_prediction('BR(Bs->mumu)') and flavio.sm_uncertainty('BR(Bs->mumu)')"
        ∷ "flavio Wilson coefficient labels C9/C10 and C9_bsll/C10_bsll are concrete authority candidates"
        ∷ "flavio package artifact, runtime environment, and parameter-card digests are explicit required slots and remain absent"
        ∷ "C9/C10 Wilson authority digest is an explicit required sha256 slot and remains absent"
        ∷ "C10/Wilson obligations and theory-uncertainty components are explicit before any empirical comparison"
        ∷ "Fail closed: no accepted authority token, comparison, anomaly claim, or promotion is constructed here"
        ∷ []
    }

canonicalWilsonAuthorityNamesFlavioVersion :
  providerDocumentationVersion canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  "2.7.0"
canonicalWilsonAuthorityNamesFlavioVersion =
  refl

canonicalWilsonAuthorityNamesFlavioDigestPackage :
  flavioProviderVersionDigest canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  canonicalFlavioProviderVersionDigest
canonicalWilsonAuthorityNamesFlavioDigestPackage =
  refl

canonicalWilsonAuthorityStillFailClosed :
  acceptedAuthorityTokenConstructedHere
    canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  false
canonicalWilsonAuthorityStillFailClosed =
  refl

canonicalWilsonAuthorityC10Obligations :
  c10WilsonObligations canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  canonicalC10WilsonObligations
canonicalWilsonAuthorityC10Obligations =
  refl

canonicalWilsonAuthorityTheoryUncertainty :
  theoryUncertaintyComponents canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  canonicalTheoryUncertaintyComponents
canonicalWilsonAuthorityTheoryUncertainty =
  refl

canonicalWilsonAuthorityNoPromotion :
  promotionConstructedHere canonicalPenguinDecayWilsonCoefficientAuthority
  ≡
  false
canonicalWilsonAuthorityNoPromotion =
  refl
