module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound3Exact where

------------------------------------------------------------------------
-- ROUND 3 BIDI SEARCH: TWO SAME-ACTION FRONTS, NO NUMERICAL PROMOTION
--
-- Round 2 isolated ActualZetaSectorRecognition as the live MN3B scientific
-- leaf.  Subsequent owners sharpened two downstream/parallel action tests:
--
--   (A) the literal Fin 90 coordinate must inherit the SAME actual inertia
--       action before the existing 12 + 78 recognition may be promoted;
--
--   (B) the 54 -> 1 + 53 branch now has a typed five-mode/nonary candidate
--       skeleton, but an actual Monster promotion requires the 53 action to be
--       the restriction of the SAME actual 54 action.
--
-- This file is search-state bookkeeping only.  It does not inhabit either
-- actual action-recognition record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound2Exact as R2
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Ninety
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as FiftyFour

------------------------------------------------------------------------
-- 1. Round-3 leaves.
------------------------------------------------------------------------

data Round3Leaf : Set where
  actualZetaActionRecognition : Round3Leaf
  actualFin90InertiaAttachment : Round3Leaf
  actualTwelveSeventyEightSameActionSplit : Round3Leaf
  typedFiftyFourFiveModeSkeleton : Round3Leaf
  actualFiftyFourResidualActionRecognition : Round3Leaf
  actualFiveModeMonsterIdentification : Round3Leaf

data LeafState : Set where
  closed generated open blocked : LeafState

leafState : Round3Leaf → LeafState
leafState actualZetaActionRecognition = open
leafState actualFin90InertiaAttachment = blocked
leafState actualTwelveSeventyEightSameActionSplit = blocked
leafState typedFiftyFourFiveModeSkeleton = generated
leafState actualFiftyFourResidualActionRecognition = open
leafState actualFiveModeMonsterIdentification = blocked

------------------------------------------------------------------------
-- 2. The MN3B highest-alpha leaf remains the actual action recognition.
------------------------------------------------------------------------

highestImpactMN3BLeaf : Round3Leaf
highestImpactMN3BLeaf = actualZetaActionRecognition

highestImpactMN3BLeafIsOpen :
  leafState highestImpactMN3BLeaf ≡ open
highestImpactMN3BLeafIsOpen = refl

round2HighestLeafAgrees :
  R2.highestImpactScientificLeaf ≡ R2.actualActionRecognition
round2HighestLeafAgrees = refl

------------------------------------------------------------------------
-- 3. The 54 lane is now structurally generated but scientifically open.
------------------------------------------------------------------------

typedFiftyFourSkeletonIsGenerated :
  leafState typedFiftyFourFiveModeSkeleton ≡ generated
typedFiftyFourSkeletonIsGenerated = refl

actualFiftyFourResidualActionIsOpen :
  leafState actualFiftyFourResidualActionRecognition ≡ open
actualFiftyFourResidualActionIsOpen = refl

fiveModeMonsterIdentificationWaitsForActualAction :
  leafState actualFiveModeMonsterIdentification ≡ blocked
fiveModeMonsterIdentificationWaitsForActualAction = refl

------------------------------------------------------------------------
-- 4. The 90 lane is action-first too: 12 + 78 cannot be promoted before the
-- literal Fin 90 coordinate has the same actual inertia action attached.
------------------------------------------------------------------------

actualFin90AttachmentWaitsForZetaRecognition :
  leafState actualFin90InertiaAttachment ≡ blocked
actualFin90AttachmentWaitsForZetaRecognition = refl

actualTwelveSeventyEightWaitsForSameAction :
  leafState actualTwelveSeventyEightSameActionSplit ≡ blocked
actualTwelveSeventyEightWaitsForSameAction = refl

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record Round3Boundary : Set where
  constructor round3-boundary
  field
    typedFiftyFourSkeletonAvailable : Bool
    typedFiveFactorAutomaticallyMonsterSemantic : Bool
    fiftyThreeRequiresSameFiftyFourActionRestriction : Bool
    fin90RequiresSameActualInertiaAction : Bool
    twelvePlusSeventyEightCanUseParallelConvenientAction : Bool
    actualZetaRecognitionStillOpen : Bool
    actualFiftyFourResidualRecognitionStillOpen : Bool
    numericFactorizationClosesEitherActualActionLeaf : Bool

canonicalRound3Boundary : Round3Boundary
canonicalRound3Boundary =
  round3-boundary
    true false true true false true true false
