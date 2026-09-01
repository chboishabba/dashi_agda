module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound2Exact where

------------------------------------------------------------------------
-- ROUND 2 BIDI SEARCH: AFTER ORDINARY IRREDUCIBILITY MACHINERY IS OUTSOURCED
--
-- Search policy: standard finite-dimensional subspace/projector or finite
-- delta-synthesis machinery is assumed available outside the Monster-specific
-- frontier.  This does NOT turn an unverified kernel receipt into a theorem;
-- it only prevents generic linear algebra from occupying the scientific search
-- frontier.
--
-- The live Monster-local object is now ActualZetaSectorRecognition:
--
--   ActualSector <-> X6 x Fin 90
--
-- with translation and modulation-exponent intertwining.  Once that object is
-- supplied, Base369 recognition follows by composition with the already-owned
-- appraisal-fibre <-> X6 chart.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact as R1
import DASHI.Moonshine.Monster3BFiniteSchrodingerIrreducibilityBidiCutExact as Irred
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Kernel
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369

------------------------------------------------------------------------
-- 1. Search-policy authority: ordinary finite-dimensional machinery is no
--    longer a Monster-specific research leaf.
------------------------------------------------------------------------

record OrdinaryIrreducibilityMachineryAssumed : Set₁ where
  constructor ordinary-irreducibility-machinery-assumed
  field
    irreducibilityAuthority : Irred.SchrodingerIrreducibilityAuthority
open OrdinaryIrreducibilityMachineryAssumed public

------------------------------------------------------------------------
-- 2. Character isotypy and action recognition remain distinct.
------------------------------------------------------------------------

record ActualKernelIsotypyAuthority : Set₁ where
  constructor actual-kernel-isotypy-authority
  field
    promotion : Kernel.ActualKernelCharacterPromotion
    ninetyCopyCharacterIsotypy :
      Kernel.NinetyHeisenbergCharacterIsotypy promotion
open ActualKernelIsotypyAuthority public

fromActualKernelPromotion :
  (promotion : Kernel.ActualKernelCharacterPromotion) → ActualKernelIsotypyAuthority
fromActualKernelPromotion promotion =
  actual-kernel-isotypy-authority promotion
    (Kernel.actualZetaSectorIsNinetyHeisenbergCopies promotion)

------------------------------------------------------------------------
-- 3. The genuine representation-theoretic recognition target.
------------------------------------------------------------------------

record ActualActionRecognitionAuthority : Set₁ where
  constructor actual-action-recognition-authority
  field
    ActualSector : Set
    recognition : Actual.ActualZetaSectorRecognition ActualSector
open ActualActionRecognitionAuthority public

base369RecognitionFromActualAction :
  (authority : ActualActionRecognitionAuthority) →
  Base369.ActualBase369SectorRecognition (ActualSector authority)
base369RecognitionFromActualAction authority =
  Base369.composeActualRecognitionWithBase369 (recognition authority)

------------------------------------------------------------------------
-- 4. Search state after BIDI pruning.
------------------------------------------------------------------------

data Round2Leaf : Set where
  ordinarySchrodingerIrreducibility : Round2Leaf
  actualKernelCharacterIsotypy : Round2Leaf
  actualActionRecognition : Round2Leaf
  base369ActionRecognition : Round2Leaf
  structuredFiftyThreeResidual : Round2Leaf

data LeafState : Set where
  outsourced closed open generated blocked : LeafState

leafState : Round2Leaf → LeafState
leafState ordinarySchrodingerIrreducibility = outsourced
leafState actualKernelCharacterIsotypy = closed
leafState actualActionRecognition = open
leafState base369ActionRecognition = generated
leafState structuredFiftyThreeResidual = blocked

highestImpactScientificLeaf : Round2Leaf
highestImpactScientificLeaf = actualActionRecognition

highestImpactScientificLeafIsOpen :
  leafState highestImpactScientificLeaf ≡ open
highestImpactScientificLeafIsOpen = refl

base369RecognitionIsGeneratedNotIndependent :
  leafState base369ActionRecognition ≡ generated
base369RecognitionIsGeneratedNotIndependent = refl

------------------------------------------------------------------------
-- 5. Exact boundary.
------------------------------------------------------------------------

record Round2Boundary : Set where
  constructor round2-boundary
  field
    ordinaryLinearAlgebraRemovedFromScientificSearch : Bool
    actualKernelCharacterIsotypyInterfaceOwned : Bool
    actualActionRecognitionConstructedHere : Bool
    base369RecognitionGeneratedFromActualRecognition : Bool
    characterEqualityPromotedDirectlyToIntertwiner : Bool
    dimensionEqualityPromotedDirectlyToIntertwiner : Bool
    fiftyThreeResidualPromotedBeforeActionRecognition : Bool
open Round2Boundary public

canonicalRound2Boundary : Round2Boundary
canonicalRound2Boundary =
  round2-boundary true true false true false false false
