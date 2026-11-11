module DASHI.Foundations.TernaryThirteenOriginalHeisenbergRelationalImageExact where

------------------------------------------------------------------------
-- H1.01: SOURCE FINITE HEISENBERG GROUP OPERATION ON THE ACTUAL
-- SELECTED IMAGE WITHIN THE ORIGINAL 144-ORDERED-RELATION FIELD.
--
-- The selected image has 12 original diagonal values, the directed
-- (0,1) central relation, and all remaining original relation cells
-- fixed neutral. It inherits the ORIGINAL nonabelian Heisenberg
-- cocycle multiplication through an explicitly invertible selected
-- group-word encoding.
--
-- IMPORTANT: the induced operation is defined on the selected image,
-- NOT asserted to preserve arbitrary original 144-cell relations,
-- relational appraisal semantics, or external-world/Monster actions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.TernaryThirteenOriginalHeisenbergGroupCarrierExact as Group
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Codec
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

sourceGroupToOriginalRelation :
  H.Heisenberg6 → Original.StageRelationField
sourceGroupToOriginalRelation g =
  Boundary.selectedRelationFromCentral (Group.originalGroupToSource g)

originalRelationToSelectedGroup :
  Original.StageRelationField → H.Heisenberg6
originalRelationToSelectedGroup field =
  Group.wordToOriginalGroup (Boundary.relationToThirteen field)

-- Both original coordinate stages use the same 13-code:
-- selected relation image -> original relation observer -> exact
-- original finite group round trip.
originalGroupRecoveredFromSelectedRelation :
  (g : H.Heisenberg6) →
  originalRelationToSelectedGroup (sourceGroupToOriginalRelation g)
  ≡ g
originalGroupRecoveredFromSelectedRelation g =
  trans
    (cong Group.wordToOriginalGroup
      (Boundary.selectedRelationThirteenCodeRoundTrip
        (Group.originalGroupToSource g)))
    (Group.originalGroupSourceRoundTrip g)

-- Every original finite Heisenberg element inhabits the genuine
-- selected IMAGE of the original 144-cell relational carrier.
groupImageIsOriginalSelectedRelation :
  (g : H.Heisenberg6) →
  Boundary.SelectedSourceRelation (sourceGroupToOriginalRelation g)
groupImageIsOriginalSelectedRelation g =
  Boundary.selectedRelationImageInhabited
    (Group.originalGroupToSource g)

-- The transported group operation on the selected image of the
-- original ordered-relation field. This is the original cocycle,
-- not coordinatewise ternary/pointwise relation addition.
selectedRelationGroupCompose :
  Original.StageRelationField →
  Original.StageRelationField →
  Original.StageRelationField
selectedRelationGroupCompose left right =
  sourceGroupToOriginalRelation
    (H.compose
      (originalRelationToSelectedGroup left)
      (originalRelationToSelectedGroup right))

selectedRelationProductIsGroupProductAt :
  (g h : H.Heisenberg6)
  (cell : Original.StageRelation144) →
  selectedRelationGroupCompose
    (sourceGroupToOriginalRelation g)
    (sourceGroupToOriginalRelation h)
    cell
  ≡ sourceGroupToOriginalRelation (H.compose g h) cell
selectedRelationProductIsGroupProductAt g h cell
  rewrite originalGroupRecoveredFromSelectedRelation g
        | originalGroupRecoveredFromSelectedRelation h = refl

selectedRelationProductIsSelected :
  (g h : H.Heisenberg6) →
  Boundary.SelectedSourceRelation
    (selectedRelationGroupCompose
      (sourceGroupToOriginalRelation g)
      (sourceGroupToOriginalRelation h))
selectedRelationProductIsSelected g h =
  H.compose g h ,
    selectedRelationProductIsGroupProductAt g h

-- The 13-coordinate group completion can therefore act on a
-- CONCRETE selected subcarrier inside the original relational
-- source, with exact group multiplication at every source cell.
-- No original arbitrary-field semantic equivalence follows.
