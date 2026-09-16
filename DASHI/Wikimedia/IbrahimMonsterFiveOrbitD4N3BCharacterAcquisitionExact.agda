module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact as Kernel
import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as N3B

------------------------------------------------------------------------
-- FIVE-ORBIT D4 CHARACTER -> N(3B) / CLASS-42 ACQUISITION FRONTIER
--
-- The kernel-side source now writes the quotient D4 permutation character
--
--   chi = (5,5,1,3,3) = 3 A1 + B1 + B2.
--
-- The Barraclough--Wilson character-table source pays the existence of the
-- N(3B) character table and its source-native inertia construction.  Current
-- repository search does not yet locate the exact 3 A1 + B1 + B2 signature as
-- a restriction of the selected Monster/N(3B) action.
--
-- Independently, ATLAS lists the Monster class 42D power family through
-- 21B, 14C, 7B, 6C, 3A and 2B.  Thus the ATLAS 42D class is not a direct
-- power-map route into class 3B.  OEIS uses the label 42d for A058678; this
-- owner deliberately does not identify the OEIS and ATLAS class labels without
-- an explicit source-bound same-class receipt.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary character-table source for N(3B); no five-orbit D4 signature identification is imported from the citation alone"
  Attribution.publicAttribution

atlasMonster : Attribution.AttributedSource
atlasMonster = Attribution.mkNoDOISource
  "ATLAS of Finite Group Representations contributors"
  "ATLAS: Monster group M -- conjugacy classes and power-up relations"
  "ATLAS of Finite Group Representations"
  "retrieved 2026-09-16"
  "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/"
  (Attribution.namedSourceKind "finite-group database record")
  "source for Monster conjugacy-class power-up relations; no OEIS-label identity or DASHI carrier identification imported"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
atlasMonsterAttribution = Snowball.canonicalSourceRoleSnowballReceipt atlasMonster

kernelBoundary : Kernel.FiveOrbitD4KernelCharacterBoundary
kernelBoundary = Kernel.currentFiveOrbitD4KernelCharacterBoundary

n3bActionFrontier : N3B.ActualLinearMultiplicityAcquisitionFrontier
n3bActionFrontier = N3B.currentActualLinearMultiplicityAcquisitionFrontier

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data OEIS42dLabelCreatesAtlas42DSameClass : Set where
data KernelD4CharacterCreatesN3BRestriction : Set where
data AtlasPowerFamilyCreatesNormalizerActionWeld : Set where

oeis42dLabelDoesNotCreateAtlas42DSameClass :
  OEIS42dLabelCreatesAtlas42DSameClass → ⊥
oeis42dLabelDoesNotCreateAtlas42DSameClass ()

kernelD4CharacterDoesNotCreateN3BRestriction :
  KernelD4CharacterCreatesN3BRestriction → ⊥
kernelD4CharacterDoesNotCreateN3BRestriction ()

atlasPowerFamilyDoesNotCreateNormalizerActionWeld :
  AtlasPowerFamilyCreatesNormalizerActionWeld → ⊥
atlasPowerFamilyDoesNotCreateNormalizerActionWeld ()

------------------------------------------------------------------------
-- Acquisition boundary.
------------------------------------------------------------------------

record FiveOrbitD4N3BCharacterAcquisition : Set where
  constructor five-orbit-d4-n3b-character-acquisition
  field
    fiveOrbitKernelCharacterSourceWritten : Bool
    quotientSignatureThreeA1B1B2Retained : Bool
    n3bCharacterTableSourceLocated : Bool
    atlas42DPowerFamilyLocated : Bool
    atlas42DFourteenthPowerTargets3A : Bool
    atlas42DDirectPowerMapTargets3B : Bool
    oeis42dAtlas42DSameClassPaid : Bool
    fiveOrbitSignatureLocatedInN3B : Bool
    selected3BNormalizerActionWeldStillRequired : Bool
    monster42dActionPaid : Bool
    nextResidual : String
open FiveOrbitD4N3BCharacterAcquisition public

currentFiveOrbitD4N3BCharacterAcquisition : FiveOrbitD4N3BCharacterAcquisition
currentFiveOrbitD4N3BCharacterAcquisition =
  five-orbit-d4-n3b-character-acquisition
    true true true true true
    false false false true false
    "First preserve the distinction between OEIS class label 42d and ATLAS class label 42D: acquire an explicit same-class nomenclature/source receipt before transferring ATLAS power-map statements to A058678. Independently search the Barraclough-Wilson N(3B) table or an actual selected normalizer action for a five-dimensional D4-stable quotient with character (5,5,1,3,3)=3*A1+B1+B2. The current ATLAS 42D power family points to 3A rather than 3B, so direct power-map-to-N(3B) is not a supported bridge. The action-level route remains the existing Selected3BNormalizerMonsterActionWeld; dimensions, labels, OEIS identities and the kernel quotient character do not create that weld."
