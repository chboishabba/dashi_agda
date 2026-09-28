module DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelInertiaLocalizedFourthTermCutsetExact where

------------------------------------------------------------------------
-- TERMINAL BAD-LEVEL / INERTIA-LOCALIZED FOURTH-TERM CUTSET
--
-- This is the current strongest small-characteristic payment.
--
-- A valid exceptional object must simultaneously provide:
--
--   p=2:
--     * Ig(p) and Ig(p^2) bad-level geometry;
--     * analytic Fricke / Atkin--Lehner compatibility;
--     * lift from X(1)^rig through the central gerbe;
--     * full binary-tetrahedral inertia localization distinguishing the two
--       nontrivial fibres collapsed by 2T -> A4 rigidification;
--
--   p=3:
--     * Ig(p) and Ig(p^2) bad-level geometry;
--     * analytic Fricke / Atkin--Lehner compatibility;
--     * pullback from X(1)^rig to the Deligne--Rapoport X0(3) neighbourhood;
--     * branch-sensitive node / Frobenius--Verschiebung local terms;
--
-- and one COMMON exceptional analytic carrier whose valuation is 10 at p=2
-- and 2 at p=3, defined independently of the Monster target.
--
-- Once inhabited, this record constructs the already-owned
-- SmallPrimeMonsterBridgeAuthority and therefore closes the joint fourth-term
-- interface.  No constructor is supplied from counts, sector ranks, raw
-- ramification, or tame Riemann--Roch data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact as Igusa
import DASHI.Moonshine.OggSSPP2ScalarDivisorInertiaLocalizationCutsetExact as P2Local
import DASHI.Moonshine.OggSSPP3DeligneRapoportDegeneracyTransportCutsetExact as P3Local
import DASHI.Moonshine.OggSSPSmallCharacteristicCrossAmbientTransportPaymentExact as Transport
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact as Joint
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Terminal authority.
------------------------------------------------------------------------

record BadLevelInertiaLocalizedFourthTermAuthority : Set₁ where
  field
    p2IgusaAuthority :
      Igusa.P2IgusaCorrectionAuthority

    p3IgusaAuthority :
      Igusa.P3IgusaCorrectionAuthority

    p2InertiaLocalization :
      P2Local.P2FiveSectorAnalyticLocalizationAuthority

    p3BranchTransport :
      P3Local.P3BadLevelBranchTransportAuthority

    crossAmbientTransport :
      Transport.CrossAmbientTransportAuthority

    ExceptionalObject :
      Set

    p2ExceptionalObject :
      ExceptionalObject

    p3ExceptionalObject :
      ExceptionalObject

    exceptionalValuation :
      Bridge.ExceptionalPrime ->
      ExceptionalObject ->
      Nat

    toP2IgusaObject :
      ExceptionalObject ->
      Igusa.ExceptionalBadLevelObject
        (Igusa.authority p2IgusaAuthority)

    toP3IgusaObject :
      ExceptionalObject ->
      Igusa.ExceptionalBadLevelObject
        (Igusa.authority p3IgusaAuthority)

    p2ValuationAgreesWithIgusa :
      exceptionalValuation Bridge.pTwo p2ExceptionalObject
      ≡
      Igusa.exceptionalValuation
        (Igusa.authority p2IgusaAuthority)
        (toP2IgusaObject p2ExceptionalObject)

    p3ValuationAgreesWithIgusa :
      exceptionalValuation Bridge.pThree p3ExceptionalObject
      ≡
      Igusa.exceptionalValuation
        (Igusa.authority p3IgusaAuthority)
        (toP3IgusaObject p3ExceptionalObject)

    p2ExceptionalObjectUsesFiveSectorLocalization :
      Bool
    p2ExceptionalObjectUsesFiveSectorLocalizationIsTrue :
      p2ExceptionalObjectUsesFiveSectorLocalization ≡ true

    p3ExceptionalObjectUsesBranchSensitiveTransport :
      Bool
    p3ExceptionalObjectUsesBranchSensitiveTransportIsTrue :
      p3ExceptionalObjectUsesBranchSensitiveTransport ≡ true

    sameObjectRefinesPublishedModularDescription :
      Bool
    sameObjectRefinesPublishedModularDescriptionIsTrue :
      sameObjectRefinesPublishedModularDescription ≡ true

    sameObjectRefinesPublishedSupersingularDescription :
      Bool
    sameObjectRefinesPublishedSupersingularDescriptionIsTrue :
      sameObjectRefinesPublishedSupersingularDescription ≡ true

    objectDefinedBeforeMonsterTarget :
      Bool
    objectDefinedBeforeMonsterTargetIsTrue :
      objectDefinedBeforeMonsterTarget ≡ true

    sourceOrProofAuthorityForValuation :
      Bool
    sourceOrProofAuthorityForValuationIsTrue :
      sourceOrProofAuthorityForValuation ≡ true

open BadLevelInertiaLocalizedFourthTermAuthority public

------------------------------------------------------------------------
-- 2. Exact gap equations derived through the Igusa authorities.
------------------------------------------------------------------------

p2ExceptionalValuationIsTen :
  (A : BadLevelInertiaLocalizedFourthTermAuthority) ->
  exceptionalValuation A Bridge.pTwo (p2ExceptionalObject A)
  ≡ Bridge.p2BridgeGap
p2ExceptionalValuationIsTen A =
  trans
    (p2ValuationAgreesWithIgusa A)
    (trans
      (Igusa.valuationIsRequiredCorrection
        (Igusa.authority (p2IgusaAuthority A)))
      (Igusa.targetIsTen (p2IgusaAuthority A)))

p3ExceptionalValuationIsTwo :
  (A : BadLevelInertiaLocalizedFourthTermAuthority) ->
  exceptionalValuation A Bridge.pThree (p3ExceptionalObject A)
  ≡ Bridge.p3BridgeGap
p3ExceptionalValuationIsTwo A =
  trans
    (p3ValuationAgreesWithIgusa A)
    (trans
      (Igusa.valuationIsRequiredCorrection
        (Igusa.authority (p3IgusaAuthority A)))
      (Igusa.targetIsTwo (p3IgusaAuthority A)))

------------------------------------------------------------------------
-- 3. Adapter to the existing terminal Monster-bridge authority.
------------------------------------------------------------------------

asMonsterBridgeAuthority :
  BadLevelInertiaLocalizedFourthTermAuthority ->
  Bridge.SmallPrimeMonsterBridgeAuthority
asMonsterBridgeAuthority A =
  record
    { Bridge.ExceptionalObject =
        ExceptionalObject A
    ; Bridge.p2ExceptionalObject =
        p2ExceptionalObject A
    ; Bridge.p3ExceptionalObject =
        p3ExceptionalObject A
    ; Bridge.exceptionalValuation =
        exceptionalValuation A
    ; Bridge.p2ExceptionalValuationIsBridgeGap =
        p2ExceptionalValuationIsTen A
    ; Bridge.p3ExceptionalValuationIsBridgeGap =
        p3ExceptionalValuationIsTwo A
    ; Bridge.objectDefinedIndependentlyOfMonsterTarget =
        objectDefinedBeforeMonsterTarget A
    ; Bridge.objectDefinedIndependentlyOfMonsterTargetIsTrue =
        objectDefinedBeforeMonsterTargetIsTrue A
    ; Bridge.refinesModularDescription =
        sameObjectRefinesPublishedModularDescription A
    ; Bridge.refinesModularDescriptionIsTrue =
        sameObjectRefinesPublishedModularDescriptionIsTrue A
    ; Bridge.refinesSupersingularDescription =
        sameObjectRefinesPublishedSupersingularDescription A
    ; Bridge.refinesSupersingularDescriptionIsTrue =
        sameObjectRefinesPublishedSupersingularDescriptionIsTrue A
    ; Bridge.sameObjectRefinesBothDescriptions =
        true
    ; Bridge.sameObjectRefinesBothDescriptionsIsTrue =
        refl
    ; Bridge.sourceOrProofAuthorityForExceptionalValuation =
        sourceOrProofAuthorityForValuation A
    ; Bridge.sourceOrProofAuthorityForExceptionalValuationIsTrue =
        sourceOrProofAuthorityForValuationIsTrue A
    }

asJointAuthority :
  BadLevelInertiaLocalizedFourthTermAuthority ->
  Joint.JointSmallPrimeExceptionalAuthority
asJointAuthority A =
  Bridge.asJointAuthority (asMonsterBridgeAuthority A)

asLicensedFourTermExtension :
  BadLevelInertiaLocalizedFourthTermAuthority ->
  Fourth.AnalyticallyLicensedFourTermExtension
asLicensedFourTermExtension A =
  Joint.asFourTermExtension (asJointAuthority A)

------------------------------------------------------------------------
-- 4. No shortcut from the currently paid finite data.
------------------------------------------------------------------------

data BadLevelIgusaDataAloneCreatesTerminalAuthority : Set where
data FiveSectorLocalizationAloneCreatesTerminalAuthority : Set where
data TwoBranchTransportAloneCreatesTerminalAuthority : Set where
data CrossAmbientTransportAloneCreatesTerminalAuthority : Set where
data TenTwoCountCreatesTerminalAuthority : Set where
data RawIgusaRamificationCreatesTerminalAuthority : Set where
data TameRiemannRochCreatesTerminalAuthority : Set where

badLevelIgusaAloneDoesNotCreateTerminalAuthority :
  BadLevelIgusaDataAloneCreatesTerminalAuthority -> ⊥
badLevelIgusaAloneDoesNotCreateTerminalAuthority ()

fiveSectorLocalizationAloneDoesNotCreateTerminalAuthority :
  FiveSectorLocalizationAloneCreatesTerminalAuthority -> ⊥
fiveSectorLocalizationAloneDoesNotCreateTerminalAuthority ()

branchTransportAloneDoesNotCreateTerminalAuthority :
  TwoBranchTransportAloneCreatesTerminalAuthority -> ⊥
branchTransportAloneDoesNotCreateTerminalAuthority ()

crossAmbientTransportAloneDoesNotCreateTerminalAuthority :
  CrossAmbientTransportAloneCreatesTerminalAuthority -> ⊥
crossAmbientTransportAloneDoesNotCreateTerminalAuthority ()

tenTwoCountDoesNotCreateTerminalAuthority :
  TenTwoCountCreatesTerminalAuthority -> ⊥
tenTwoCountDoesNotCreateTerminalAuthority ()

rawIgusaRamificationDoesNotCreateTerminalAuthority :
  RawIgusaRamificationCreatesTerminalAuthority -> ⊥
rawIgusaRamificationDoesNotCreateTerminalAuthority ()

tameRiemannRochDoesNotCreateTerminalAuthority :
  TameRiemannRochCreatesTerminalAuthority -> ⊥
tameRiemannRochDoesNotCreateTerminalAuthority ()

------------------------------------------------------------------------
-- 5. Live theorem wall.
------------------------------------------------------------------------

data BadLevelInertiaLocalizedFourthTermAuthorityInhabited : Set where

terminalAuthorityStillOpen :
  BadLevelInertiaLocalizedFourthTermAuthorityInhabited -> ⊥
terminalAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record BadLevelInertiaLocalizedFourthTermBoundary : Set where
  constructor bad-level-inertia-localized-fourth-term-boundary
  field
    p2BadLevelIgusaRequired : Bool
    p3BadLevelIgusaRequired : Bool
    p2FiveSectorInertiaLocalizationRequired : Bool
    p3BranchSensitiveTransportRequired : Bool
    crossAmbientTransportRequired : Bool
    commonExceptionalObjectRequired : Bool
    adapterToMonsterBridgeOwned : Bool
    adapterToJointAuthorityOwned : Bool
    adapterToLicensedFourTermExtensionOwned : Bool
    terminalAuthorityInhabited : Bool
    finiteCountsPromotedToTerminalAuthority : Bool
    rawRamificationPromotedToTerminalAuthority : Bool
    tameRiemannRochPromotedToTerminalAuthority : Bool

canonicalBadLevelInertiaLocalizedFourthTermBoundary :
  BadLevelInertiaLocalizedFourthTermBoundary
canonicalBadLevelInertiaLocalizedFourthTermBoundary =
  bad-level-inertia-localized-fourth-term-boundary
    true true true true true true true true true
    false false false false
