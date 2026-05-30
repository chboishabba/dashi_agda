module DASHI.Physics.Closure.YML3TightnessFromDimensionalTransmutationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CSLevelRunningLawReceipt as Running
import DASHI.Physics.Closure.StringTensionCarrierReceipt as StringTension
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as KRunning

------------------------------------------------------------------------
-- YM L3 partial tightness receipt from dimensional transmutation data.

data YML3DimensionalTransmutationStatus : Set where
  dimensionalTransmutationCandidateRecordedPartialOnly :
    YML3DimensionalTransmutationStatus

data YML3DimensionalTransmutationRoute : Set where
  runningLawCandidateRoute :
    YML3DimensionalTransmutationRoute

  standardAuthorityRouteRequirement :
    YML3DimensionalTransmutationRoute

  uniformPhysicalStringTensionCandidateRoute :
    YML3DimensionalTransmutationRoute

  l3PartialNotFullClayRoute :
    YML3DimensionalTransmutationRoute

canonicalYML3DimensionalTransmutationRoutes :
  List YML3DimensionalTransmutationRoute
canonicalYML3DimensionalTransmutationRoutes =
  runningLawCandidateRoute
  ∷ standardAuthorityRouteRequirement
  ∷ uniformPhysicalStringTensionCandidateRoute
  ∷ l3PartialNotFullClayRoute
  ∷ []

data YML3DimensionalTransmutationOpenItem : Set where
  acceptedStandardAuthorityRouteMissing :
    YML3DimensionalTransmutationOpenItem

  prokhorovTightnessProofMissing :
    YML3DimensionalTransmutationOpenItem

  continuumWilsonMeasureLimitMissing :
    YML3DimensionalTransmutationOpenItem

  fullClayYangMillsProofMissing :
    YML3DimensionalTransmutationOpenItem

canonicalYML3DimensionalTransmutationOpenItems :
  List YML3DimensionalTransmutationOpenItem
canonicalYML3DimensionalTransmutationOpenItems =
  acceptedStandardAuthorityRouteMissing
  ∷ prokhorovTightnessProofMissing
  ∷ continuumWilsonMeasureLimitMissing
  ∷ fullClayYangMillsProofMissing
  ∷ []

data YML3DimensionalTransmutationPromotion : Set where

yml3DimensionalTransmutationPromotionImpossibleHere :
  YML3DimensionalTransmutationPromotion →
  ⊥
yml3DimensionalTransmutationPromotionImpossibleHere ()

dimensionalTransmutationLawLabel : String
dimensionalTransmutationLawLabel =
  "dimensional transmutation route: k(mu)=b0/(2pi)log(mu/Lambda_c), a(k)=Lambda_c^-1 exp(-2pi k/b0), b0_SU2=22/3, Lambda_c=1.59 GeV, a(k)=exp(-3pi k/11)/Lambda_c"

uniformPhysicalStringTensionCandidateLabel : String
uniformPhysicalStringTensionCandidateLabel =
  "uniform physical string tension candidate: sigma_phys(k) = sigma_carrier(k) / a(k)^2, candidate-only until standard authority and continuum tightness are supplied"

yml3DimensionalTransmutationStatement : String
yml3DimensionalTransmutationStatement =
  "Dimensional transmutation records a candidate/standard-authority route and a uniform physical string tension candidate, giving only partial YM L3 evidence; it is not a full Clay Yang-Mills tightness or mass-gap proof."

record YML3TightnessFromDimensionalTransmutationReceipt : Setω where
  field
    status :
      YML3DimensionalTransmutationStatus

    runningLawReceipt :
      Running.CSLevelRunningLawReceipt

    runningLawCandidateRecorded :
      Running.runningLawCandidateRecorded runningLawReceipt ≡ true

    runningLawKeepsAuthorityMissing :
      Running.standardAuthorityRouteConstructed runningLawReceipt ≡ false

    runningLawKeepsClayFalse :
      Running.clayYangMillsPromoted runningLawReceipt ≡ false

    kRunningAuditReceipt :
      KRunning.YML3TightnessFromKRunningReceipt

    kRunningAuditKeepsFullTightnessFalse :
      KRunning.ymL3TightnessConstructed kRunningAuditReceipt ≡ false

    stringTensionReceipt :
      StringTension.StringTensionCarrierReceipt

    carrierStringTensionRecorded :
      StringTension.stringTensionFromStrongCoupling stringTensionReceipt
        ≡ true

    carrierStringTensionKeepsClayFalse :
      StringTension.clayYangMillsPromoted stringTensionReceipt ≡ false

    routes :
      List YML3DimensionalTransmutationRoute

    routesAreCanonical :
      routes ≡ canonicalYML3DimensionalTransmutationRoutes

    openItems :
      List YML3DimensionalTransmutationOpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalYML3DimensionalTransmutationOpenItems

    dimensionalTransmutationLaw :
      String

    dimensionalTransmutationLawIsCanonical :
      dimensionalTransmutationLaw ≡ dimensionalTransmutationLawLabel

    uniformPhysicalStringTensionCandidateStatement :
      String

    uniformPhysicalStringTensionCandidateStatementIsCanonical :
      uniformPhysicalStringTensionCandidateStatement
        ≡ uniformPhysicalStringTensionCandidateLabel

    candidateAuthorityRouteRecorded :
      Bool

    candidateAuthorityRouteRecordedIsTrue :
      candidateAuthorityRouteRecorded ≡ true

    dimensionalTransmutationKnown :
      Bool

    dimensionalTransmutationKnownIsTrue :
      dimensionalTransmutationKnown ≡ true

    standardAuthorityRouteRequired :
      Bool

    standardAuthorityRouteRequiredIsTrue :
      standardAuthorityRouteRequired ≡ true

    standardAuthorityRouteConstructed :
      Bool

    standardAuthorityRouteConstructedIsFalse :
      standardAuthorityRouteConstructed ≡ false

    uniformPhysicalStringTensionCandidateRecorded :
      Bool

    uniformPhysicalStringTensionCandidateRecordedIsTrue :
      uniformPhysicalStringTensionCandidateRecorded ≡ true

    uniformPhysicalStringTensionProved :
      Bool

    uniformPhysicalStringTensionProvedIsFalse :
      uniformPhysicalStringTensionProved ≡ false

    l3PartialEvidenceRecorded :
      Bool

    l3PartialEvidenceRecordedIsTrue :
      l3PartialEvidenceRecorded ≡ true

    fullL3TightnessConstructed :
      Bool

    fullL3TightnessConstructedIsFalse :
      fullL3TightnessConstructed ≡ false

    prokhorovTightnessConstructed :
      Bool

    prokhorovTightnessConstructedIsFalse :
      prokhorovTightnessConstructed ≡ false

    continuumWilsonMeasureConstructed :
      Bool

    continuumWilsonMeasureConstructedIsFalse :
      continuumWilsonMeasureConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ yml3DimensionalTransmutationStatement

    promotionFlags :
      List YML3DimensionalTransmutationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML3TightnessFromDimensionalTransmutationReceipt public

canonicalYML3TightnessFromDimensionalTransmutationReceipt :
  YML3TightnessFromDimensionalTransmutationReceipt
canonicalYML3TightnessFromDimensionalTransmutationReceipt =
  record
    { status =
        dimensionalTransmutationCandidateRecordedPartialOnly
    ; runningLawReceipt =
        Running.canonicalCSLevelRunningLawReceipt
    ; runningLawCandidateRecorded =
        refl
    ; runningLawKeepsAuthorityMissing =
        refl
    ; runningLawKeepsClayFalse =
        refl
    ; kRunningAuditReceipt =
        KRunning.canonicalYML3TightnessFromKRunningReceipt
    ; kRunningAuditKeepsFullTightnessFalse =
        refl
    ; stringTensionReceipt =
        StringTension.canonicalStringTensionCarrierReceipt
    ; carrierStringTensionRecorded =
        refl
    ; carrierStringTensionKeepsClayFalse =
        refl
    ; routes =
        canonicalYML3DimensionalTransmutationRoutes
    ; routesAreCanonical =
        refl
    ; openItems =
        canonicalYML3DimensionalTransmutationOpenItems
    ; openItemsAreCanonical =
        refl
    ; dimensionalTransmutationLaw =
        dimensionalTransmutationLawLabel
    ; dimensionalTransmutationLawIsCanonical =
        refl
    ; uniformPhysicalStringTensionCandidateStatement =
        uniformPhysicalStringTensionCandidateLabel
    ; uniformPhysicalStringTensionCandidateStatementIsCanonical =
        refl
    ; candidateAuthorityRouteRecorded =
        true
    ; candidateAuthorityRouteRecordedIsTrue =
        refl
    ; dimensionalTransmutationKnown =
        true
    ; dimensionalTransmutationKnownIsTrue =
        refl
    ; standardAuthorityRouteRequired =
        true
    ; standardAuthorityRouteRequiredIsTrue =
        refl
    ; standardAuthorityRouteConstructed =
        false
    ; standardAuthorityRouteConstructedIsFalse =
        refl
    ; uniformPhysicalStringTensionCandidateRecorded =
        true
    ; uniformPhysicalStringTensionCandidateRecordedIsTrue =
        refl
    ; uniformPhysicalStringTensionProved =
        false
    ; uniformPhysicalStringTensionProvedIsFalse =
        refl
    ; l3PartialEvidenceRecorded =
        true
    ; l3PartialEvidenceRecordedIsTrue =
        refl
    ; fullL3TightnessConstructed =
        false
    ; fullL3TightnessConstructedIsFalse =
        refl
    ; prokhorovTightnessConstructed =
        false
    ; prokhorovTightnessConstructedIsFalse =
        refl
    ; continuumWilsonMeasureConstructed =
        false
    ; continuumWilsonMeasureConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        yml3DimensionalTransmutationStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records dimensional transmutation as a candidate route plus required standard authority route"
        ∷ "Records dimensional transmutation as known/candidate/partial, not as a full Clay proof"
        ∷ "Records k(mu), a(k), b0_SU2=22/3, Lambda_c=1.59 GeV, mu_k, and k=1/k=5 estimates through the running-law receipt"
        ∷ "Records a uniform physical string tension candidate only"
        ∷ "YM L3 evidence is partial; full tightness, Prokhorov compactness, and continuum Wilson measure construction remain open"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

yml3DimensionalTransmutationKeepsFullTightnessFalse :
  fullL3TightnessConstructed
    canonicalYML3TightnessFromDimensionalTransmutationReceipt ≡ false
yml3DimensionalTransmutationKeepsFullTightnessFalse =
  refl

yml3DimensionalTransmutationKeepsClayFalse :
  clayYangMillsPromoted
    canonicalYML3TightnessFromDimensionalTransmutationReceipt ≡ false
yml3DimensionalTransmutationKeepsClayFalse =
  refl

yml3DimensionalTransmutationKeepsTerminalFalse :
  terminalClayClaimPromoted
    canonicalYML3TightnessFromDimensionalTransmutationReceipt ≡ false
yml3DimensionalTransmutationKeepsTerminalFalse =
  refl
