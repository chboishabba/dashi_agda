module DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact where

------------------------------------------------------------------------
-- ARICHETA HIGHER-LEVEL OGG BRIDGE: BAD-LEVEL DIAGONAL CUTSET
--
-- EXTERNAL SOURCE
--
-- Victor Manuel Aricheta, "Supersingular Elliptic Curves and Moonshine",
-- SIGMA 15 (2019), 007, DOI 10.3842/SIGMA.2019.007.
--
-- Theorem 3.3:
--   For a monstrous modular curve X of level N and a prime p with p ∤ N,
--   the supersingular rationality property for X is equivalent to the
--   centralizer of g in C(X) containing a Fricke element of order p.
--
-- Remark 3.5:
--   the paper explicitly asks whether the theory can be extended to primes
--   dividing the level so that the moonshine/centralizer theorems generalize.
--
-- OUR TWO SMALL-PRIME LANES ARE EXACTLY THE EXCLUDED DIAGONAL:
--
--   2B : X_0(2), p = 2,
--   3B : X_0(3), p = 3.
--
-- Therefore Aricheta is a direct source for the OFF-DIAGONAL
-- supersingular-level <-> Monster-centralizer bridge, and simultaneously a
-- source-backed NO-GO against silently applying that theorem to our p=N lanes.
--
-- Kobin--Zureick-Brown (2025) then explains why p=2,3 are structurally
-- exceptional: X(1) and level towers are wildly stacky in these
-- characteristics.  This supports the need for a genuinely bad-level
-- extension, but does not itself prove the Monster-local 10/2 valuation.
--
-- ATTRIBUTION:
--   Aricheta owns the p ∤ N bridge and the open extension question.
--   Kobin--Zureick-Brown own the modern wild-stack geometry.
--   DASHI owns only the synthesis that our 2B/3B lanes lie precisely on the
--   missing p|N diagonal and the resulting typed extension obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact as Padic
import DASHI.Moonshine.OggSSP2B3BPrimeLevelBaselineSameObjectExact as PrimeBaseline
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source atlas.
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
    "Theorem 3.3 sources the supersingular-level/rationality <-> Monster-centralizer Fricke bridge under p not dividing N; Remark 3.5 explicitly leaves the p-divides-level extension open"
    Source.publicAttribution

kobinZureickBrown : Source.AttributedSource
kobinZureickBrown =
  Source.mkNoDOISource
    "Andrew Kobin and David Zureick-Brown"
    "Wild Stacky Curves and Rings of Mod p Modular Forms"
    "arXiv:2510.08821"
    "2025"
    "https://arxiv.org/abs/2510.08821"
    Source.academicArticleSource
    "sources genuinely wild stack structure for modular stacks in characteristics 2 and 3 and propagation through level towers; does not prove the DASHI Monster-local valuation bridge"
    Source.publicAttribution

arichetaBadLevelSourceAtlas : Source.AttributedSourceAtlas
arichetaBadLevelSourceAtlas =
  Source.mkSourceAtlas
    "Aricheta higher-level Ogg bridge / bad-level diagonal cutset"
    "DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact"
    (aricheta ∷ kobinZureickBrown ∷ [])
    "Aricheta owns the off-diagonal p-not-dividing-N centralizer theorem and explicitly open diagonal extension; Kobin--Zureick-Brown own the wild small-prime geometry; DASHI owns only the typed identification of 2B/3B as the excluded diagonal"

------------------------------------------------------------------------
-- 2. The two target lanes.
------------------------------------------------------------------------

data SmallPrimeDiagonalLane : Set where
  lane2B lane3B : SmallPrimeDiagonalLane

lanePrime : SmallPrimeDiagonalLane -> Nat
lanePrime lane2B = 2
lanePrime lane3B = 3

laneLevel : SmallPrimeDiagonalLane -> Nat
laneLevel lane2B = 2
laneLevel lane3B = 3

laneClass :
  SmallPrimeDiagonalLane ->
  Padic.SmallPrimeMonsterClass
laneClass lane2B = Padic.class2B
laneClass lane3B = Padic.class3B

primeEqualsLevel :
  (lane : SmallPrimeDiagonalLane) ->
  lanePrime lane ≡ laneLevel lane
primeEqualsLevel lane2B = refl
primeEqualsLevel lane3B = refl

classLevelAgreesWithLane :
  (lane : SmallPrimeDiagonalLane) ->
  Padic.hauptmodulLevel (laneClass lane)
  ≡ laneLevel lane
classLevelAgreesWithLane lane2B = refl
classLevelAgreesWithLane lane3B = refl

------------------------------------------------------------------------
-- 3. Aricheta applicability grading.
------------------------------------------------------------------------

data ArichetaApplicability : Set where
  offDiagonalHypothesisSatisfied :
    ArichetaApplicability
  badLevelDiagonalExcluded :
    ArichetaApplicability

arichetaApplicability :
  SmallPrimeDiagonalLane ->
  ArichetaApplicability
arichetaApplicability lane2B = badLevelDiagonalExcluded
arichetaApplicability lane3B = badLevelDiagonalExcluded

data ArichetaTheorem33DirectlyAppliesTo2BAtP2 : Set where
data ArichetaTheorem33DirectlyAppliesTo3BAtP3 : Set where

arichetaTheorem33DoesNotDirectlyApplyTo2BAtP2 :
  ArichetaTheorem33DirectlyAppliesTo2BAtP2 -> ⊥
arichetaTheorem33DoesNotDirectlyApplyTo2BAtP2 ()

arichetaTheorem33DoesNotDirectlyApplyTo3BAtP3 :
  ArichetaTheorem33DirectlyAppliesTo3BAtP3 -> ⊥
arichetaTheorem33DoesNotDirectlyApplyTo3BAtP3 ()

------------------------------------------------------------------------
-- 4. The exact missing external theorem shape.
--
-- This is intentionally weaker than the final valuation theorem.  It first
-- asks for the bad-level analogue of Aricheta's centralizer recognition on
-- the p=N diagonal.  A later analytic refinement must still compute the
-- source-native valuation and show it is the independently defined 10/2
-- Monster-local defect.
------------------------------------------------------------------------

record BadLevelArichetaCentralizerExtensionAuthority : Set₁ where
  field
    BadLevelObject : Set

    p2BadLevelObject :
      BadLevelObject

    p3BadLevelObject :
      BadLevelObject

    p2ComesFromLevelTwoSupersingularGeometry :
      Bool
    p2ComesFromLevelTwoSupersingularGeometryIsTrue :
      p2ComesFromLevelTwoSupersingularGeometry ≡ true

    p3ComesFromLevelThreeSupersingularGeometry :
      Bool
    p3ComesFromLevelThreeSupersingularGeometryIsTrue :
      p3ComesFromLevelThreeSupersingularGeometry ≡ true

    handlesPrimeDividingLevel :
      Bool
    handlesPrimeDividingLevelIsTrue :
      handlesPrimeDividingLevel ≡ true

    p2RecognisesMonster2BCentralizerFrickeData :
      Bool
    p2RecognisesMonster2BCentralizerFrickeDataIsTrue :
      p2RecognisesMonster2BCentralizerFrickeData ≡ true

    p3RecognisesMonster3BCentralizerFrickeData :
      Bool
    p3RecognisesMonster3BCentralizerFrickeDataIsTrue :
      p3RecognisesMonster3BCentralizerFrickeData ≡ true

    compatibleWithBadLevelFrickeAtkinLehner :
      Bool
    compatibleWithBadLevelFrickeAtkinLehnerIsTrue :
      compatibleWithBadLevelFrickeAtkinLehner ≡ true

    sameObjectCarriesSupersingularAndCentralizerDescriptions :
      Bool
    sameObjectCarriesSupersingularAndCentralizerDescriptionsIsTrue :
      sameObjectCarriesSupersingularAndCentralizerDescriptions ≡ true

    sourceOrProofIndependentOfTargetTenTwo :
      Bool
    sourceOrProofIndependentOfTargetTenTwoIsTrue :
      sourceOrProofIndependentOfTargetTenTwo ≡ true

open BadLevelArichetaCentralizerExtensionAuthority public

data BadLevelArichetaExtensionAlreadyInLiterature : Set where
data WildStackGeometryAutomaticallyProvesBadLevelCentralizerBridge : Set where
data OffDiagonalArichetaTheoremMayBeUsedOnDiagonalWithoutProof : Set where

badLevelArichetaExtensionNotClaimedFromCurrentLiterature :
  BadLevelArichetaExtensionAlreadyInLiterature -> ⊥
badLevelArichetaExtensionNotClaimedFromCurrentLiterature ()

wildStackGeometryDoesNotAutomaticallyProveCentralizerBridge :
  WildStackGeometryAutomaticallyProvesBadLevelCentralizerBridge -> ⊥
wildStackGeometryDoesNotAutomaticallyProveCentralizerBridge ()

offDiagonalArichetaTheoremCannotBeSilentlyUsedOnDiagonal :
  OffDiagonalArichetaTheoremMayBeUsedOnDiagonalWithoutProof -> ⊥
offDiagonalArichetaTheoremCannotBeSilentlyUsedOnDiagonal ()

------------------------------------------------------------------------
-- 5. Existing same-object prime-level receipt.
------------------------------------------------------------------------

primeLevelSameObjectBoundary :
  PrimeBaseline.PrimeLevelBaselineSameObjectBoundary
primeLevelSameObjectBoundary =
  PrimeBaseline.canonicalPrimeLevelBaselineSameObjectBoundary

------------------------------------------------------------------------
-- 6. Live boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record ArichetaBadLevelDiagonalBoundary : Set where
  constructor aricheta-bad-level-diagonal-boundary
  field
    arichetaOffDiagonalCentralizerBridgeSourced : Bool
    arichetaPrimeNotDividingLevelHypothesisRecorded : Bool
    arichetaRemarkLeavesBadLevelExtensionOpen : Bool
    class2BLevelTwoSameObjectSourced : Bool
    class3BLevelThreeSameObjectSourced : Bool
    p2EqualsLevelTwo : Bool
    p3EqualsLevelThree : Bool
    theorem33DirectlyAppliesToP2Lane : Bool
    theorem33DirectlyAppliesToP3Lane : Bool
    wildSmallPrimeGeometrySourced : Bool
    badLevelExtensionAuthoritySpecified : Bool
    badLevelExtensionAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalArichetaBadLevelDiagonalBoundary :
  ArichetaBadLevelDiagonalBoundary
canonicalArichetaBadLevelDiagonalBoundary =
  aricheta-bad-level-diagonal-boundary
    true true true true true true true
    false false true true false true
