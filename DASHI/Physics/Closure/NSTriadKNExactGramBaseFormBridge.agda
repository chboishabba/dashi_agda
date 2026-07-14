module DASHI.Physics.Closure.NSTriadKNExactGramBaseFormBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_; _<_)

import DASHI.Physics.Closure.NSTriadKN369HighHighGramBridgeReceipt as Bridge369
import DASHI.Physics.Closure.NSTriadKNExactAlgebraicDefinitionReceipt as ExactDef
import DASHI.Physics.Closure.NSTriadKNExactIdentityReceipt as ExactIdentity
import DASHI.Physics.Closure.NSTriadKNGate2ANormalizedCarrierAgreementReceipt as CarrierAgreement
import DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt as GramReceipt
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseFormBridge as GramRayleighBridge
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- The exact base-form parent should be pinned to the exact K_N(A) object lane,
-- not left as a free quadratic-form slot. This bridge exposes the minimum
-- theorem-facing content needed to feed ExactGramBaseFormIdentification from
-- the repo's exact-algebraic-definition route.

record ExactKNAPositiveSubspaceCarrierTarget
    (Carrier : Set)
    : Setω where
  constructor mkExactKNAPositiveSubspaceCarrierTarget
  field
    exactDefinitionReceipt :
      ExactDef.NSTriadKNExactAlgebraicDefinitionReceipt

    exactIdentityReceipt :
      ExactIdentity.NSTriadKNExactIdentityReceipt

    carrierAgreementReceipt :
      CarrierAgreement.NSTriadKNGate2ANormalizedCarrierAgreementReceipt

    gramCoercivityReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    bridge369Receipt :
      Bridge369.NSTriadKN369HighHighGramBridgeReceipt

    exactDefinitionRecorded :
      ExactDef.exactKDefinitionWritten exactDefinitionReceipt ≡ true

    scriptObjectMatched :
      ExactDef.scriptObjectMatched exactDefinitionReceipt ≡ true

    exactIdentityRecorded :
      ExactIdentity.exactIdentityRecordedHere exactIdentityReceipt ≡ true

    exactIdentityFailClosed :
      ExactIdentity.failClosed exactIdentityReceipt ≡ true

    carrierAgreementRecorded :
      CarrierAgreement.gate2aCarrierSpacesIdentified carrierAgreementReceipt ≡ true

    exactRestrictionIdentityRecorded :
      CarrierAgreement.gate2aExactRestrictionIdentityObserved carrierAgreementReceipt ≡ true

    gramCoercivityRecorded :
      GramReceipt.failClosed gramCoercivityReceipt ≡ true

    bridge369Recorded :
      Bridge369.failClosed bridge369Receipt ≡ true

open ExactKNAPositiveSubspaceCarrierTarget public

canonicalExactKNAPositiveSubspaceCarrierTarget :
  {Carrier : Set} →
  ExactKNAPositiveSubspaceCarrierTarget Carrier
canonicalExactKNAPositiveSubspaceCarrierTarget {Carrier} =
  mkExactKNAPositiveSubspaceCarrierTarget
    ExactDef.canonicalNSTriadKNExactAlgebraicDefinitionReceipt
    ExactIdentity.canonicalNSTriadKNExactIdentityReceipt
    CarrierAgreement.canonicalNSTriadKNGate2ANormalizedCarrierAgreementReceipt
    GramReceipt.canonicalNSTriadKNGramCoercivityTargetReceipt
    Bridge369.canonicalNSTriadKN369HighHighGramBridgeReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record ExactKNABaseQuadraticFormIdentificationTarget
    (Carrier : Set)
    : Setω where
  constructor mkExactKNABaseQuadraticFormIdentificationTarget
  field
    positiveSubspaceCarrier :
      ExactKNAPositiveSubspaceCarrierTarget Carrier

    baseQuadraticForm :
      Carrier → Nat

open ExactKNABaseQuadraticFormIdentificationTarget public

toExactKNABaseQuadraticFormIdentificationTarget :
  {Carrier : Set} →
  ExactKNAPositiveSubspaceCarrierTarget Carrier →
  (Carrier → Nat) →
  ExactKNABaseQuadraticFormIdentificationTarget Carrier
toExactKNABaseQuadraticFormIdentificationTarget positiveSubspaceCarrier baseQuadraticForm =
  mkExactKNABaseQuadraticFormIdentificationTarget
    positiveSubspaceCarrier
    baseQuadraticForm

record ExactKNAGramRayleighCore
    (Carrier : Set)
    (shellIndex : Nat)
    (strongNormSquared : Carrier → Nat)
    (stage3ErrorConstant : Nat)
    : Setω where
  constructor mkExactKNAGramRayleighCore
  field
    baseQuadraticForm :
      Carrier → Nat

    baseGapConstant : Nat
    baseGapPositive : Set
    compatibilityScale : ScaleHeadroom.CompatibilityScale shellIndex

    rayleighBaseCoercive :
      (x : Carrier) →
      baseGapConstant * strongNormSquared x
        ≤
        ScaleHeadroom.CompatibilityScale.scaleSq compatibilityScale
          * baseQuadraticForm x

    stage3ErrorBelowBaseGap :
      stage3ErrorConstant < baseGapConstant

open ExactKNAGramRayleighCore public

toExactKNABaseQuadraticFormIdentificationFromCore :
  {Carrier : Set} →
  {shellIndex : Nat} →
  {strongNormSquared : Carrier → Nat} →
  {stage3ErrorConstant : Nat} →
  ExactKNAPositiveSubspaceCarrierTarget Carrier →
  ExactKNAGramRayleighCore
    Carrier
    shellIndex
    strongNormSquared
    stage3ErrorConstant →
  ExactKNABaseQuadraticFormIdentificationTarget Carrier
toExactKNABaseQuadraticFormIdentificationFromCore
  positiveSubspaceCarrier
  core =
  mkExactKNABaseQuadraticFormIdentificationTarget
    positiveSubspaceCarrier
    (ExactKNAGramRayleighCore.baseQuadraticForm core)

record ExactKNAQuadraticCarrierTarget
    (Carrier : Set)
    : Setω where
  constructor mkExactKNAQuadraticCarrierTarget
  field
    positiveSubspaceCarrier :
      ExactKNAPositiveSubspaceCarrierTarget Carrier

    baseFormIdentification :
      ExactKNABaseQuadraticFormIdentificationTarget Carrier

open ExactKNAQuadraticCarrierTarget public

record ExactKNAObjectDefinitionTarget
    (Carrier : Set)
    : Setω where
  constructor mkExactKNAObjectDefinitionTarget
  field
    gramCoercivityReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    exactDefinitionReceipt :
      ExactDef.NSTriadKNExactAlgebraicDefinitionReceipt

    bridge369Receipt :
      Bridge369.NSTriadKN369HighHighGramBridgeReceipt

    gramCoercivityRecorded :
      GramReceipt.failClosed gramCoercivityReceipt ≡ true

    exactDefinitionRecorded :
      ExactDef.exactKDefinitionWritten exactDefinitionReceipt ≡ true

    scriptObjectMatched :
      ExactDef.scriptObjectMatched exactDefinitionReceipt ≡ true

    bridge369Recorded :
      Bridge369.failClosed bridge369Receipt ≡ true

    baseQuadraticForm :
      Carrier → Nat

open ExactKNAObjectDefinitionTarget public

toExactKNAObjectDefinitionTarget :
  {Carrier : Set} →
  ExactKNAQuadraticCarrierTarget Carrier →
  ExactKNAObjectDefinitionTarget Carrier
toExactKNAObjectDefinitionTarget target =
  mkExactKNAObjectDefinitionTarget
    (ExactKNAPositiveSubspaceCarrierTarget.gramCoercivityReceipt
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.exactDefinitionReceipt
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.bridge369Receipt
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.gramCoercivityRecorded
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.exactDefinitionRecorded
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.scriptObjectMatched
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNAPositiveSubspaceCarrierTarget.bridge369Recorded
      (ExactKNAQuadraticCarrierTarget.positiveSubspaceCarrier target))
    (ExactKNABaseQuadraticFormIdentificationTarget.baseQuadraticForm
      (ExactKNAQuadraticCarrierTarget.baseFormIdentification target))

toExactGramBaseFormIdentification :
  {Carrier : Set} →
  ExactKNAObjectDefinitionTarget Carrier →
  GramRayleighBridge.ExactGramBaseFormIdentification Carrier
toExactGramBaseFormIdentification target =
  GramRayleighBridge.mkExactGramBaseFormIdentification
    (ExactKNAObjectDefinitionTarget.gramCoercivityReceipt target)
    (ExactKNAObjectDefinitionTarget.gramCoercivityRecorded target)
    (ExactKNAObjectDefinitionTarget.baseQuadraticForm target)
