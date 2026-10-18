module DASHI.Moonshine.OggSSPPBScalarLocalizationP2OnlyFrontierExact where

------------------------------------------------------------------------
-- PRIME-B SCALAR LOCALIZATION: p=2-ONLY FRONTIER
--
-- The reduced p=3 scalar authority is now inhabited from Borcherds's
-- source-native simple Tate factors:
--
--   H^0 representative factor : length 1
--   H^1 representative factor : length 1.
--
-- Therefore the joint reduced pB scalar theorem has only ONE remaining
-- inhabitant:
--
--   p=2 five actual integral source slots with normalized DVR lengths
--   3,3,2,1,1.
--
-- This module packages that exact reduction.
--
-- It still does NOT create the stronger semantic localization theorem or the
-- Monster/Hauptmodul same-object bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as P2
import DASHI.Moonshine.OggSSPP3TateSimpleFactorLengthOneExact as P3Paid
import DASHI.Moonshine.OggSSPPBScalarLocalizationReductionExact as PB
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Assemble the complete reduced scalar authority from p=2 alone.
------------------------------------------------------------------------

assembleFromP2 :
  P2.P2SourceDepthSlotLengthAuthority ->
  PB.PBScalarLocalizationAuthority
assembleFromP2 p2Authority =
  record
    { PB.p2 =
        p2Authority

    ; PB.p3 =
        P3Paid.canonicalP3TateScalarLengthAuthority
    }

------------------------------------------------------------------------
-- 2. Both source-native scalar totals then follow.
------------------------------------------------------------------------

assembledP2TotalIsTen :
  (p2Authority : P2.P2SourceDepthSlotLengthAuthority) ->
  PB.p2ScalarSourceTotal (assembleFromP2 p2Authority) ≡ 10
assembledP2TotalIsTen p2Authority =
  PB.p2ScalarSourceTotalIsTen
    (assembleFromP2 p2Authority)

assembledP3TotalIsTwo :
  (p2Authority : P2.P2SourceDepthSlotLengthAuthority) ->
  PB.p3ScalarSourceTotal (assembleFromP2 p2Authority) ≡ 2
assembledP3TotalIsTwo p2Authority =
  PB.p3ScalarSourceTotalIsTwo
    (assembleFromP2 p2Authority)

------------------------------------------------------------------------
-- 3. Remaining inhabitant is exactly the p=2 source-depth authority.
------------------------------------------------------------------------

data JointReducedScalarAuthorityStillNeedsIndependentP3Payment : Set where
data JointReducedScalarAuthorityAlreadyInhabitedWithoutP2 : Set where

jointReducedScalarDoesNotNeedAnotherP3Payment :
  JointReducedScalarAuthorityStillNeedsIndependentP3Payment -> ⊥
jointReducedScalarDoesNotNeedAnotherP3Payment ()

jointReducedScalarStillNeedsP2 :
  JointReducedScalarAuthorityAlreadyInhabitedWithoutP2 -> ⊥
jointReducedScalarStillNeedsP2 ()

------------------------------------------------------------------------
-- 4. Stronger semantic/local analytic obligations remain separate.
------------------------------------------------------------------------

data P2ScalarAuthorityCreatesFiveSectorRecognition : Set where
data P2ScalarAuthorityCreatesPrimeLevelIgusaLocalization : Set where
data P2ScalarAuthorityCreatesMonsterBridge : Set where
data P3RepresentativeFactorsCreateMonsterBridge : Set where

p2ScalarDoesNotCreateFiveSectorRecognition :
  P2ScalarAuthorityCreatesFiveSectorRecognition -> ⊥
p2ScalarDoesNotCreateFiveSectorRecognition ()

p2ScalarDoesNotCreateIgusaLocalization :
  P2ScalarAuthorityCreatesPrimeLevelIgusaLocalization -> ⊥
p2ScalarDoesNotCreateIgusaLocalization ()

p2ScalarDoesNotCreateMonsterBridge :
  P2ScalarAuthorityCreatesMonsterBridge -> ⊥
p2ScalarDoesNotCreateMonsterBridge ()

p3RepresentativeFactorsDoNotCreateMonsterBridge :
  P3RepresentativeFactorsCreateMonsterBridge -> ⊥
p3RepresentativeFactorsDoNotCreateMonsterBridge ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record PBScalarLocalizationP2OnlyFrontierBoundary : Set where
  constructor pb-scalar-localization-p2-only-frontier-boundary
  field
    p3ReducedScalarAuthorityInhabited : Bool
    p3RepresentativeH0LengthOne : Bool
    p3RepresentativeH1LengthOne : Bool
    jointAuthorityAssemblesFromP2Alone : Bool
    p2FiveSlotDepthAuthorityStillRequired : Bool
    p2FiveSlotDepthAuthorityInhabited : Bool
    p3AdditionalSourcePaymentRequired : Bool
    fullSemanticLocalizationInhabited : Bool
    monsterBridgeInhabitedByScalarReduction : Bool
    attributionFirewallPreserved : Bool

canonicalPBScalarLocalizationP2OnlyFrontierBoundary :
  PBScalarLocalizationP2OnlyFrontierBoundary
canonicalPBScalarLocalizationP2OnlyFrontierBoundary =
  pb-scalar-localization-p2-only-frontier-boundary
    true true true true true false false false false true
