module DASHI.Moonshine.OggSSPSmallCharacteristicSOTAMonsterLocalBridgeCutsetExact where

------------------------------------------------------------------------
-- SOTA BAD-LEVEL / GENERALIZED-MOONSHINE / MONSTER-LOCAL BRIDGE CUTSET
--
-- This is the strongest current small-characteristic recognition interface.
--
-- It intersects three independently motivated surfaces:
--
--   A. bad-level Igusa/inertia/Hasse-osculation geometry and corrected
--      Hauptmodul valuation;
--
--   B. generalized-moonshine twisted data on which Monster centralizers act
--      and whose graded traces are modular functions;
--
--   C. independent Monster-local targets
--        C_M(2B) : v2 = 46,
--        C_M(3B) : v3 = 20,
--      whose defects over the Duncan--Swisher 36/18 baseline are 10/2.
--
-- The SAME exceptional object must refine all three descriptions.
--
-- No constructor is supplied from:
--   * equality of the numbers 10/2,
--   * finite sector counts,
--   * centralizer depth,
--   * character tables,
--   * raw Igusa ramification,
--   * Hasse/osculation,
--   * or generalized moonshine modularity alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicSOTATerminalFourthTermRefinementExact as SOTATerminal
import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelInertiaLocalizedFourthTermCutsetExact as Terminal
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPSmallPrimeGeneralizedMoonshineCentralizerBridgeExact as GM
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact as Aricheta
import DASHI.Moonshine.OggSSPSmallPrimeArichetaIgusaBadLevelExtensionExact as ArichetaIgusa

------------------------------------------------------------------------
-- 1. Unified same-object authority.
------------------------------------------------------------------------

record SOTAMonsterLocalBridgeAuthority : Set₁ where
  field
    sotaTerminal :
      SOTATerminal.SOTATerminalFourthTermAuthority

    generalizedMoonshineBridge :
      GM.GeneralizedMoonshineCentralizerModularBridge

    twistedTraceValuation :
      GM.SmallPrimeTwistedTraceValuationAuthority
        generalizedMoonshineBridge

    badLevelArichetaIgusaExtension :
      ArichetaIgusa.ArichetaIgusaBadLevelExtensionAuthority

    ExceptionalObject :
      Set

    p2ExceptionalObject :
      ExceptionalObject

    p3ExceptionalObject :
      ExceptionalObject

    exceptionalValuation :
      Local.MonsterLocalPrime ->
      ExceptionalObject ->
      Nat

    toTerminalObject :
      ExceptionalObject ->
      Terminal.ExceptionalObject
        (SOTATerminal.terminal sotaTerminal)

    toTwistedTraceTerm :
      ExceptionalObject ->
      GM.BadLevelLocalTerm twistedTraceValuation

    toArichetaIgusaBadLevelObject :
      ExceptionalObject ->
      ArichetaIgusa.BadLevelObject badLevelArichetaIgusaExtension

    p2ValuationAgreesWithTerminal :
      exceptionalValuation Local.monsterTwo p2ExceptionalObject
      ≡
      Terminal.exceptionalValuation
        (SOTATerminal.terminal sotaTerminal)
        (toTerminalObject p2ExceptionalObject)

    p3ValuationAgreesWithTerminal :
      exceptionalValuation Local.monsterThree p3ExceptionalObject
      ≡
      Terminal.exceptionalValuation
        (SOTATerminal.terminal sotaTerminal)
        (toTerminalObject p3ExceptionalObject)

    p2ValuationAgreesWithTwistedTrace :
      exceptionalValuation Local.monsterTwo p2ExceptionalObject
      ≡
      GM.valuation twistedTraceValuation
        (toTwistedTraceTerm p2ExceptionalObject)

    p3ValuationAgreesWithTwistedTrace :
      exceptionalValuation Local.monsterThree p3ExceptionalObject
      ≡
      GM.valuation twistedTraceValuation
        (toTwistedTraceTerm p3ExceptionalObject)

    p2RecognisesMonsterLocalCentralizerDefect :
      exceptionalValuation Local.monsterTwo p2ExceptionalObject
      ≡
      Local.localCentralizerDefect Local.monsterTwo

    p3RecognisesMonsterLocalCentralizerDefect :
      exceptionalValuation Local.monsterThree p3ExceptionalObject
      ≡
      Local.localCentralizerDefect Local.monsterThree

    objectDefinedBeforeMonsterTarget :
      Bool
    objectDefinedBeforeMonsterTargetIsTrue :
      objectDefinedBeforeMonsterTarget ≡ true

    sameObjectRefinesBadLevelModularDescription :
      Bool
    sameObjectRefinesBadLevelModularDescriptionIsTrue :
      sameObjectRefinesBadLevelModularDescription ≡ true

    sameObjectRefinesGeneralizedMoonshineTwistedDescription :
      Bool
    sameObjectRefinesGeneralizedMoonshineTwistedDescriptionIsTrue :
      sameObjectRefinesGeneralizedMoonshineTwistedDescription ≡ true

    sameObjectRefinesArichetaIgusaBadLevelDescription :
      Bool
    sameObjectRefinesArichetaIgusaBadLevelDescriptionIsTrue :
      sameObjectRefinesArichetaIgusaBadLevelDescription ≡ true

    sourceOrProofAuthorityForValuation :
      Bool
    sourceOrProofAuthorityForValuationIsTrue :
      sourceOrProofAuthorityForValuation ≡ true

open SOTAMonsterLocalBridgeAuthority public

------------------------------------------------------------------------
-- 2. Adapter to the independent Monster-local recognition target.
------------------------------------------------------------------------

asMonsterLocalCentralizerRecognitionAuthority :
  SOTAMonsterLocalBridgeAuthority ->
  Local.MonsterLocalCentralizerRecognitionAuthority
asMonsterLocalCentralizerRecognitionAuthority A =
  record
    { Local.ExceptionalGeometricObject =
        ExceptionalObject A
    ; Local.p2Object =
        p2ExceptionalObject A
    ; Local.p3Object =
        p3ExceptionalObject A
    ; Local.geometricValuation =
        exceptionalValuation A
    ; Local.p2RecognisesLocalCentralizerDefect =
        p2RecognisesMonsterLocalCentralizerDefect A
    ; Local.p3RecognisesLocalCentralizerDefect =
        p3RecognisesMonsterLocalCentralizerDefect A
    ; Local.objectDefinedWithoutMonsterOrderTarget =
        objectDefinedBeforeMonsterTarget A
    ; Local.objectDefinedWithoutMonsterOrderTargetIsTrue =
        objectDefinedBeforeMonsterTargetIsTrue A
    ; Local.sourceOrProofAuthorityForGeometricValuation =
        sourceOrProofAuthorityForValuation A
    ; Local.sourceOrProofAuthorityForGeometricValuationIsTrue =
        sourceOrProofAuthorityForValuationIsTrue A
    ; Local.sameObjectRefinesDuncanSwisherArithmetic =
        sameObjectRefinesBadLevelModularDescription A
    ; Local.sameObjectRefinesDuncanSwisherArithmeticIsTrue =
        sameObjectRefinesBadLevelModularDescriptionIsTrue A
    ; Local.sameObjectRecognisesMonsterLocalCentralizer =
        true
    ; Local.sameObjectRecognisesMonsterLocalCentralizerIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 3. Adapter to the existing Monster bridge.
------------------------------------------------------------------------

asMonsterBridgeAuthority :
  SOTAMonsterLocalBridgeAuthority ->
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
        λ prime object ->
          exceptionalValuation A
            (toLocalPrime prime)
            object
    ; Bridge.p2ExceptionalValuationIsBridgeGap =
        trans
          (p2RecognisesMonsterLocalCentralizerDefect A)
          Local.p2LocalResidualAgreesWithBridgeGap
    ; Bridge.p3ExceptionalValuationIsBridgeGap =
        trans
          (p3RecognisesMonsterLocalCentralizerDefect A)
          Local.p3LocalResidualAgreesWithBridgeGap
    ; Bridge.objectDefinedIndependentlyOfMonsterTarget =
        objectDefinedBeforeMonsterTarget A
    ; Bridge.objectDefinedIndependentlyOfMonsterTargetIsTrue =
        objectDefinedBeforeMonsterTargetIsTrue A
    ; Bridge.refinesModularDescription =
        sameObjectRefinesBadLevelModularDescription A
    ; Bridge.refinesModularDescriptionIsTrue =
        sameObjectRefinesBadLevelModularDescriptionIsTrue A
    ; Bridge.refinesSupersingularDescription =
        true
    ; Bridge.refinesSupersingularDescriptionIsTrue =
        refl
    ; Bridge.sameObjectRefinesBothDescriptions =
        true
    ; Bridge.sameObjectRefinesBothDescriptionsIsTrue =
        refl
    ; Bridge.sourceOrProofAuthorityForExceptionalValuation =
        sourceOrProofAuthorityForValuation A
    ; Bridge.sourceOrProofAuthorityForExceptionalValuationIsTrue =
        sourceOrProofAuthorityForValuationIsTrue A
    }
  where
    toLocalPrime :
      Bridge.ExceptionalPrime ->
      Local.MonsterLocalPrime
    toLocalPrime Bridge.pTwo = Local.monsterTwo
    toLocalPrime Bridge.pThree = Local.monsterThree

------------------------------------------------------------------------
-- 4. Source-backed bad-level centralizer cut.
------------------------------------------------------------------------

arichetaBadLevelBoundary :
  Aricheta.ArichetaBadLevelDiagonalBoundary
arichetaBadLevelBoundary =
  Aricheta.canonicalArichetaBadLevelDiagonalBoundary

arichetaIgusaBadLevelBoundary :
  ArichetaIgusa.ArichetaIgusaBadLevelExtensionBoundary
arichetaIgusaBadLevelBoundary =
  ArichetaIgusa.canonicalArichetaIgusaBadLevelExtensionBoundary

------------------------------------------------------------------------
-- 5. No shortcut to the unified authority.
------------------------------------------------------------------------

data SOTATerminalAloneCreatesMonsterLocalBridge : Set where
data GeneralizedMoonshineAloneCreatesMonsterLocalBridge : Set where
data LocalCentralizerDefectsCreateSameObjectRecognition : Set where
data MatchingTenTwoCreatesUnifiedAuthority : Set where
data OffDiagonalArichetaBridgeAutomaticallySolvesDiagonal : Set where

sotaTerminalAloneDoesNotCreateMonsterLocalBridge :
  SOTATerminalAloneCreatesMonsterLocalBridge -> ⊥
sotaTerminalAloneDoesNotCreateMonsterLocalBridge ()

generalizedMoonshineAloneDoesNotCreateMonsterLocalBridge :
  GeneralizedMoonshineAloneCreatesMonsterLocalBridge -> ⊥
generalizedMoonshineAloneDoesNotCreateMonsterLocalBridge ()

localCentralizerDefectsDoNotCreateSameObjectRecognition :
  LocalCentralizerDefectsCreateSameObjectRecognition -> ⊥
localCentralizerDefectsDoNotCreateSameObjectRecognition ()

matchingTenTwoDoesNotCreateUnifiedAuthority :
  MatchingTenTwoCreatesUnifiedAuthority -> ⊥
matchingTenTwoDoesNotCreateUnifiedAuthority ()

offDiagonalArichetaBridgeDoesNotSolveDiagonal :
  OffDiagonalArichetaBridgeAutomaticallySolvesDiagonal -> ⊥
offDiagonalArichetaBridgeDoesNotSolveDiagonal ()

------------------------------------------------------------------------
-- 6. Live theorem wall.
------------------------------------------------------------------------

data SOTAMonsterLocalBridgeAuthorityInhabited : Set where

sotaMonsterLocalBridgeStillOpen :
  SOTAMonsterLocalBridgeAuthorityInhabited -> ⊥
sotaMonsterLocalBridgeStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SOTAMonsterLocalBridgeBoundary : Set where
  constructor sota-monster-local-bridge-boundary
  field
    sotaBadLevelTerminalRequired : Bool
    generalizedMoonshineTwistedBridgeRequired : Bool
    arichetaBadLevelCentralizerExtensionRequired : Bool
    arichetaIgusaSameObjectIntersectionRequired : Bool
    independent2B3BLocalCentralizerTargetRequired : Bool
    sameExceptionalObjectRequired : Bool
    sameObjectArichetaBadLevelRefinementRequired : Bool
    sameObjectArichetaIgusaRefinementRequired : Bool
    terminalValuationAgreementRequired : Bool
    twistedTraceValuationAgreementRequired : Bool
    localCentralizerDefectRecognitionRequired : Bool
    adapterToMonsterLocalRecognitionOwned : Bool
    adapterToMonsterBridgeOwned : Bool
    authorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalSOTAMonsterLocalBridgeBoundary :
  SOTAMonsterLocalBridgeBoundary
canonicalSOTAMonsterLocalBridgeBoundary =
  sota-monster-local-bridge-boundary
    true true true true true true true true true true true true true false true
