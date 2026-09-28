module DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact where

------------------------------------------------------------------------
-- DVR-LENGTH / GENERALIZED-BRAUER CUTSET
--
-- EXTERNAL SOURCE
--
-- Satoru Urano, "A Composite Order Generalization of Modular Moonshine"
-- (SIGMA 17 (2021), 110):
--
--   * generalizes Brauer characters to arbitrary finite-length modules over
--     discrete valuation rings;
--   * proves that generalized super Brauer characters of Tate cohomology are
--     linear combinations of ordinary trace functions.
--
-- This is exactly the TYPE of mixed-characteristic invariant needed after the
-- Carnahan integral pB Tate-cohomology bridge: finite-length DVR data can carry
-- both a length/valuation observable and a trace-function character.
--
-- ATTRIBUTION FIREWALL
--
-- Urano does NOT state:
--   * the 2B defect is 10;
--   * the 3B defect is 2;
--   * the relevant finite-length object is the p=N Igusa localization;
--   * the Monster valuation is the raw DVR length.
--
-- DASHI therefore uses Urano only to sharpen the terminal authority from
-- "some Nat-valued valuation" to a finite-length-DVR / generalized-Brauer
-- localization theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

uranoCompositeOrder : Source.AttributedSource
uranoCompositeOrder =
  Source.mkDOISource
    "Satoru Urano"
    "A Composite Order Generalization of Modular Moonshine"
    "SIGMA 17 (2021), 110"
    "2021"
    "10.3842/SIGMA.2021.110"
    "https://doi.org/10.3842/SIGMA.2021.110"
    Source.academicArticleSource
    "introduces generalized Brauer characters for arbitrary finite-length modules over discrete valuation rings and proves generalized super Brauer characters of Tate cohomology are linear combinations of trace functions; used only as the mixed-characteristic invariant framework, not as a source for the DASHI 10/2 valuation"
    Source.publicAttribution

dvrBrauerSourceAtlas : Source.AttributedSourceAtlas
dvrBrauerSourceAtlas =
  Source.mkSourceAtlas
    "finite-length DVR generalized-Brauer localization cutset"
    "DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact"
    (uranoCompositeOrder ∷ [])
    "Urano owns finite-length DVR generalized Brauer-character theory; DASHI owns the proposed specialization to pB bad-level localization and the 10/2 recognition target"

------------------------------------------------------------------------
-- 2. Sourced structural receipt.
------------------------------------------------------------------------

record DVRGeneralizedBrauerReceipt : Set where
  constructor dvr-generalized-brauer-receipt
  field
    arbitraryFiniteLengthDVRModulesSupported : Bool
    generalizedBrauerCharacterDefined : Bool
    tateSuperBrauerCharacterIsTraceCombination : Bool
    mixedCharacteristicLengthAndTraceCanCoexist : Bool

canonicalDVRGeneralizedBrauerReceipt :
  DVRGeneralizedBrauerReceipt
canonicalDVRGeneralizedBrauerReceipt =
  dvr-generalized-brauer-receipt
    true true true true

------------------------------------------------------------------------
-- 3. Prime-specific residual target remains independent.
------------------------------------------------------------------------

data SmallPrimePB : Set where
  p2B p3B : SmallPrimePB

targetResidual :
  SmallPrimePB ->
  Nat
targetResidual p2B =
  Local.p2LocalCentralizerResidual
targetResidual p3B =
  Local.p3LocalCentralizerResidual

p2TargetIsTen :
  targetResidual p2B ≡ 10
p2TargetIsTen = refl

p3TargetIsTwo :
  targetResidual p3B ≡ 2
p3TargetIsTwo = refl

------------------------------------------------------------------------
-- 4. Sharpened terminal theorem target.
------------------------------------------------------------------------

record PBLocalizedDVRBrauerAuthority : Set₁ where
  field
    LocalizedTateModule : Set

    p2LocalizedModule :
      LocalizedTateModule

    p3LocalizedModule :
      LocalizedTateModule

    isFiniteLengthOverRelevantDVR :
      SmallPrimePB ->
      LocalizedTateModule ->
      Bool

    p2FiniteLength :
      isFiniteLengthOverRelevantDVR p2B p2LocalizedModule ≡ true

    p3FiniteLength :
      isFiniteLengthOverRelevantDVR p3B p3LocalizedModule ≡ true

    comesFromCarnahanPBIntegralTateObject :
      Bool
    comesFromCarnahanPBIntegralTateObjectIsTrue :
      comesFromCarnahanPBIntegralTateObject ≡ true

    localizedAtPrimeEqualsLevelIgusaObject :
      Bool
    localizedAtPrimeEqualsLevelIgusaObjectIsTrue :
      localizedAtPrimeEqualsLevelIgusaObject ≡ true

    preservesPBMonsterLocalCentralizerAction :
      Bool
    preservesPBMonsterLocalCentralizerActionIsTrue :
      preservesPBMonsterLocalCentralizerAction ≡ true

    generalizedBrauerCharacterAgreesWithPBTrace :
      Bool
    generalizedBrauerCharacterAgreesWithPBTraceIsTrue :
      generalizedBrauerCharacterAgreesWithPBTrace ≡ true

    lengthFunctional :
      SmallPrimePB ->
      LocalizedTateModule ->
      Nat

    p2LengthPaysResidual :
      lengthFunctional p2B p2LocalizedModule
      ≡ targetResidual p2B

    p3LengthPaysResidual :
      lengthFunctional p3B p3LocalizedModule
      ≡ targetResidual p3B

    lengthFunctionalDerivedWithoutReadingTarget :
      Bool
    lengthFunctionalDerivedWithoutReadingTargetIsTrue :
      lengthFunctionalDerivedWithoutReadingTarget ≡ true

open PBLocalizedDVRBrauerAuthority public

data PBLocalizedDVRBrauerAuthorityInhabited : Set where

pbLocalizedDVRBrauerAuthorityStillOpen :
  PBLocalizedDVRBrauerAuthorityInhabited -> ⊥
pbLocalizedDVRBrauerAuthorityStillOpen ()

------------------------------------------------------------------------
-- 5. Scope firewalls.
------------------------------------------------------------------------

data UranoProvesPBResidualTenTwo : Set where
data FiniteLengthAutomaticallyEqualsMonsterDefect : Set where
data TraceCombinationAutomaticallyDefinesIgusaLocalization : Set where
data DVRFrameworkAloneInhabitsTerminalAuthority : Set where

uranoDoesNotProvePBResidualTenTwo :
  UranoProvesPBResidualTenTwo -> ⊥
uranoDoesNotProvePBResidualTenTwo ()

finiteLengthDoesNotAutomaticallyEqualMonsterDefect :
  FiniteLengthAutomaticallyEqualsMonsterDefect -> ⊥
finiteLengthDoesNotAutomaticallyEqualMonsterDefect ()

traceCombinationDoesNotAutomaticallyDefineIgusaLocalization :
  TraceCombinationAutomaticallyDefinesIgusaLocalization -> ⊥
traceCombinationDoesNotAutomaticallyDefineIgusaLocalization ()

dvrFrameworkAloneDoesNotInhabitTerminalAuthority :
  DVRFrameworkAloneInhabitsTerminalAuthority -> ⊥
dvrFrameworkAloneDoesNotInhabitTerminalAuthority ()

------------------------------------------------------------------------
-- 6. Existing integral pB source receipt.
------------------------------------------------------------------------

pbIntegralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
pbIntegralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record DVRLengthBrauerCutsetBoundary : Set where
  constructor dvr-length-brauer-cutset-boundary
  field
    uranoFiniteLengthDVRBrauerFrameworkSourced : Bool
    uranoTateTraceCombinationTheoremSourced : Bool
    carnahanPBIntegralTateObjectSourced : Bool
    finiteLengthLocalizationAuthoritySpecified : Bool
    finiteLengthLocalizationAuthorityInhabited : Bool
    uranoCreditedWithTenTwo : Bool
    rawLengthPromotedToMonsterDefectWithoutProof : Bool
    attributionFirewallPreserved : Bool

canonicalDVRLengthBrauerCutsetBoundary :
  DVRLengthBrauerCutsetBoundary
canonicalDVRLengthBrauerCutsetBoundary =
  dvr-length-brauer-cutset-boundary
    true true true true false false false true
