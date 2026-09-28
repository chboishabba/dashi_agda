module DASHI.Moonshine.OggSSPSmallPrimeExternalBridgeDoubleMismatchExact where

------------------------------------------------------------------------
-- SMALL-PRIME EXTERNAL-BRIDGE DOUBLE MISMATCH
--
-- Two of the strongest external bridges each approach the live 2B/3B wall,
-- but from different sides.
--
-- ARICHETA (2019)
--   * supplies a supersingular-level <-> Monster-centralizer Fricke theorem;
--   * hypothesis: p does NOT divide the level N;
--   * our target lanes are diagonal bad-level:
--         2B : p=N=2,
--         3B : p=N=3.
--
-- CHEN--MARKS--TYLER (2019)
--   * supply p-adic/weakly-p-adic Hauptmodul machinery at p=2,3;
--   * T_2B and T_3B themselves have sourced p-adic behavior;
--   * their sourced Monster-centralizer construction in Section 5.3 concerns
--     centralizers of pA-pure elementary abelian subgroups of order p^2,
--     not the C_M(2B) / C_M(3B) local-centralizer targets.
--
-- Therefore the two papers cannot be silently composed into the desired
-- theorem.  A genuinely new bridge must fix BOTH mismatches at once:
--
--   pB conjugacy class + p=N bad level + supersingular/Igusa geometry
--     + twisted/p-adic local trace + Monster-local valuation.
--
-- Attribution is fail-closed:
--   external papers own only the theorems inside their published hypotheses;
--   DASHI owns this applicability intersection and the resulting obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact as Aricheta
import DASHI.Moonshine.OggSSPSmallPrimePadicMoonshineScopeCutsetExact as CMT
import DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact as Padic
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sources.
------------------------------------------------------------------------

aricheta : Source.AttributedSource
aricheta =
  Source.mkDOISource
    "Victor Manuel Aricheta"
    "Supersingular Elliptic Curves and Moonshine"
    "SIGMA 15 (2019), 007"
    "2019"
    "10.3842/SIGMA.2019.007"
    "https://doi.org/10.3842/SIGMA.2019.007"
    Source.academicArticleSource
    "Theorem 3.3 gives the supersingular-level/Monster-centralizer Fricke bridge under p not dividing N; Remark 3.5 leaves the p-divides-N extension open"
    Source.publicAttribution

chenMarksTyler : Source.AttributedSource
chenMarksTyler =
  Source.mkDOISource
    "Ryan C. Chen, Samuel Marks, and Matthew Tyler"
    "p-adic Properties of Hauptmoduln with Applications to Moonshine"
    "SIGMA 15 (2019), 033"
    "2019"
    "10.3842/SIGMA.2019.033"
    "https://doi.org/10.3842/SIGMA.2019.033"
    Source.academicArticleSource
    "sources p-adic/weakly-p-adic monstrous Hauptmodul behavior and Section 5.3 centralizers of pA-pure elementary abelian p^2 subgroups; does not identify the 2B/3B local-centralizer valuation target"
    Source.publicAttribution

doubleMismatchSourceAtlas : Source.AttributedSourceAtlas
doubleMismatchSourceAtlas =
  Source.mkSourceAtlas
    "small-prime Aricheta/CMT applicability double mismatch"
    "DASHI.Moonshine.OggSSPSmallPrimeExternalBridgeDoubleMismatchExact"
    (aricheta ∷ chenMarksTyler ∷ [])
    "Aricheta owns the off-diagonal supersingular/centralizer bridge; Chen--Marks--Tyler own the p-adic Hauptmodul and pA-pure centralizer results; DASHI owns only the applicability intersection and missing pB bad-level theorem"

------------------------------------------------------------------------
-- 2. Typed target lanes.
------------------------------------------------------------------------

data SmallPrimeLane : Set where
  lane2B lane3B : SmallPrimeLane

lanePrime : SmallPrimeLane -> Nat
lanePrime lane2B = 2
lanePrime lane3B = 3

laneLevel : SmallPrimeLane -> Nat
laneLevel lane2B = 2
laneLevel lane3B = 3

data MonsterPrimeClassFamily : Set where
  familyA familyB : MonsterPrimeClassFamily

laneClassFamily : SmallPrimeLane -> MonsterPrimeClassFamily
laneClassFamily lane2B = familyB
laneClassFamily lane3B = familyB

primeEqualsLevel :
  (lane : SmallPrimeLane) ->
  lanePrime lane ≡ laneLevel lane
primeEqualsLevel lane2B = refl
primeEqualsLevel lane3B = refl

------------------------------------------------------------------------
-- 3. Published-theorem applicability matrix.
------------------------------------------------------------------------

data PublishedBridge : Set where
  arichetaOffDiagonal :
    PublishedBridge
  cmtPAElementaryAbelianCentralizer :
    PublishedBridge
  cmtIndividualPBHauptmodul :
    PublishedBridge

data ApplicabilityFailure : Set where
  primeDividesLevel :
    ApplicabilityFailure
  wrongMonsterClassFamily :
    ApplicabilityFailure
  noCentralizerSameObjectTheorem :
    ApplicabilityFailure

arichetaFailure :
  (lane : SmallPrimeLane) ->
  ApplicabilityFailure
arichetaFailure lane =
  primeDividesLevel

cmtCentralizerFailure :
  (lane : SmallPrimeLane) ->
  ApplicabilityFailure
cmtCentralizerFailure lane =
  wrongMonsterClassFamily

cmtIndividualHauptmodulFailure :
  (lane : SmallPrimeLane) ->
  ApplicabilityFailure
cmtIndividualHauptmodulFailure lane =
  noCentralizerSameObjectTheorem

------------------------------------------------------------------------
-- 4. Exact firewalls.
------------------------------------------------------------------------

data ArichetaDirectlyClosesP2Diagonal : Set where
data ArichetaDirectlyClosesP3Diagonal : Set where
data CMTPACentralizerIsC2BLocalCentralizer : Set where
data CMTPACentralizerIsC3BLocalCentralizer : Set where
data IndividualPBPadicAnnihilationCreatesPBLocalCentralizerTheorem : Set where
data TwoPartialExternalBridgesComposeAutomatically : Set where

arichetaDoesNotDirectlyCloseP2Diagonal :
  ArichetaDirectlyClosesP2Diagonal -> ⊥
arichetaDoesNotDirectlyCloseP2Diagonal ()

arichetaDoesNotDirectlyCloseP3Diagonal :
  ArichetaDirectlyClosesP3Diagonal -> ⊥
arichetaDoesNotDirectlyCloseP3Diagonal ()

cmtPACentralizerIsNotC2BTarget :
  CMTPACentralizerIsC2BLocalCentralizer -> ⊥
cmtPACentralizerIsNotC2BTarget ()

cmtPACentralizerIsNotC3BTarget :
  CMTPACentralizerIsC3BLocalCentralizer -> ⊥
cmtPACentralizerIsNotC3BTarget ()

individualPBPadicBehaviorDoesNotCreateLocalCentralizerTheorem :
  IndividualPBPadicAnnihilationCreatesPBLocalCentralizerTheorem -> ⊥
individualPBPadicBehaviorDoesNotCreateLocalCentralizerTheorem ()

partialBridgesDoNotComposeAcrossApplicabilityGaps :
  TwoPartialExternalBridgesComposeAutomatically -> ⊥
partialBridgesDoNotComposeAcrossApplicabilityGaps ()

------------------------------------------------------------------------
-- 5. The exact missing theorem shape.
------------------------------------------------------------------------

record PBBadLevelPadicCentralizerAuthority : Set₁ where
  field
    ExceptionalObject : Set

    p2Object :
      ExceptionalObject
    p3Object :
      ExceptionalObject

    handlesPrimeDividingLevel :
      Bool
    handlesPrimeDividingLevelIsTrue :
      handlesPrimeDividingLevel ≡ true

    targetsPBClassFamily :
      Bool
    targetsPBClassFamilyIsTrue :
      targetsPBClassFamily ≡ true

    refinesSupersingularBadLevelGeometry :
      Bool
    refinesSupersingularBadLevelGeometryIsTrue :
      refinesSupersingularBadLevelGeometry ≡ true

    refinesClassSpecificPadicHauptmodul :
      Bool
    refinesClassSpecificPadicHauptmodulIsTrue :
      refinesClassSpecificPadicHauptmodul ≡ true

    refinesPBMonsterLocalCentralizer :
      Bool
    refinesPBMonsterLocalCentralizerIsTrue :
      refinesPBMonsterLocalCentralizer ≡ true

    carriesSourceNativeValuation :
      Bool
    carriesSourceNativeValuationIsTrue :
      carriesSourceNativeValuation ≡ true

    valuationIndependentOfTargetTenTwo :
      Bool
    valuationIndependentOfTargetTenTwoIsTrue :
      valuationIndependentOfTargetTenTwo ≡ true

open PBBadLevelPadicCentralizerAuthority public

data PBBadLevelPadicCentralizerAuthorityInhabited : Set where

pbBadLevelPadicCentralizerAuthorityStillOpen :
  PBBadLevelPadicCentralizerAuthorityInhabited -> ⊥
pbBadLevelPadicCentralizerAuthorityStillOpen ()

------------------------------------------------------------------------
-- 6. Existing source-boundary receipts.
------------------------------------------------------------------------

arichetaBoundary :
  Aricheta.ArichetaBadLevelDiagonalBoundary
arichetaBoundary =
  Aricheta.canonicalArichetaBadLevelDiagonalBoundary

cmtScopeBoundary :
  CMT.SmallPrimePadicMoonshineScopeBoundary
cmtScopeBoundary =
  CMT.canonicalSmallPrimePadicMoonshineScopeBoundary

padicHauptmodulBoundary :
  Padic.ClassSpecificPadicHauptmodulBridgeBoundary
padicHauptmodulBoundary =
  Padic.canonicalClassSpecificPadicHauptmodulBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record ExternalBridgeDoubleMismatchBoundary : Set where
  constructor external-bridge-double-mismatch-boundary
  field
    arichetaOffDiagonalBridgeSourced : Bool
    arichetaBadLevelDiagonalExcluded : Bool
    cmtPBHauptmodulPadicBehaviorSourced : Bool
    cmtCentralizerTheoremTargetsPAPureSubgroups : Bool
    targetLaneIsPBFamily : Bool
    arichetaLevelMismatchExplicit : Bool
    cmtClassFamilyMismatchExplicit : Bool
    individualPadicBehaviorInsufficientForCentralizerRecognition : Bool
    twoPartialBridgesAutomaticallyCompose : Bool
    pbBadLevelPadicCentralizerAuthoritySpecified : Bool
    pbBadLevelPadicCentralizerAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalExternalBridgeDoubleMismatchBoundary :
  ExternalBridgeDoubleMismatchBoundary
canonicalExternalBridgeDoubleMismatchBoundary =
  external-bridge-double-mismatch-boundary
    true true true true true true true true false true false true
