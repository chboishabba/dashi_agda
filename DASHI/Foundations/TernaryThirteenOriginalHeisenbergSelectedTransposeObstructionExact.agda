module DASHI.Foundations.TernaryThirteenOriginalHeisenbergSelectedTransposeObstructionExact where

------------------------------------------------------------------------
-- H1.01: SAME-OBJECT SEMANTIC ACTION NEGATIVE CONTROL.
--
-- This test uses the genuinely original selected relation image,
-- the original directed 144-cell transpose, and the original
-- finite Heisenberg central-phase elements.
--
-- For the selected 13-coordinate image, transpose sends the
-- selected (0,1) centre into the *omitted* (1,0) cell. Its
-- 13-coordinate observation therefore forgets the centre.
-- Two different original central group elements map to the
-- same transposed selected relation code.
--
-- Thus that particular restricted relation transpose CANNOT
-- be an equivariant group automorphism on the full H_6 model.
-- This does not assert that every relational process is transpose
-- or that the source intended a Heisenberg group action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.TernaryThirteenOriginalHeisenbergGroupCarrierExact as Bridge
import DASHI.Foundations.TernaryThirteenOriginalHeisenbergRelationalImageExact as Image
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.TernaryThirteenOriginalRelationalTransposeDescentExact as Transpose
import DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact as Residual
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Algebra.Trit as F3
import Base369 as Base

sourceCentralZero : H.Heisenberg6
sourceCentralZero = H.central F3.zer

sourceCentralPositive : H.Heisenberg6
sourceCentralPositive = H.central F3.pos

sourceCentralElementsDiffer :
  sourceCentralZero ≡ sourceCentralPositive → ⊥
sourceCentralElementsDiffer eq = differentPhases (cong H.centralPhase eq)
  where
    differentPhases : F3.zer ≡ F3.pos → ⊥
    differentPhases ()

-- Source group -> actual selected 144-cell relation ->
-- original transpose -> selected 13-coordinate observation.
selectedTransposeCode :
  H.Heisenberg6 → Word.TritWord 13
selectedTransposeCode g =
  Boundary.relationToThirteen
    (Original.transposeRelation (Image.sourceGroupToOriginalRelation g))

-- The chosen centre after transpose is always neutral on the
-- selected original 13-dimensional relational IMAGE, since the
-- directed reverse (1,0) coordinate was fixed neutral.
selectedTransposeAlwaysNeutralCentre :
  (g : H.Heisenberg6) →
  Transpose.decodeCentral (selectedTransposeCode g)
  ≡ Base.tri-mid
selectedTransposeAlwaysNeutralCentre g =
  trans
    (Transpose.originalRelationCodeCentralRecovers
      (Original.transposeRelation (Image.sourceGroupToOriginalRelation g)))
    refl

-- An ACTUAL noninjective pair, not just a group-order count:
-- their twelve source coordinates agree, their centre differs,
-- and transpose of the source-selected 144 relation forgets it.
selectedTransposeCollapsesDifferentCentralElements :
  selectedTransposeCode sourceCentralZero
  ≡ selectedTransposeCode sourceCentralPositive
selectedTransposeCollapsesDifferentCentralElements = refl

-- Therefore no proposed action with this output can be
-- injective on source Heisenberg elements. In particular
-- it cannot implement any invertible group automorphism.
selectedTransposeCannotBeInjective :
  ((g h : H.Heisenberg6) →
    selectedTransposeCode g ≡ selectedTransposeCode h →
    g ≡ h) →
  ⊥
selectedTransposeCannotBeInjective injective =
  sourceCentralElementsDiffer
    (injective sourceCentralZero sourceCentralPositive
      selectedTransposeCollapsesDifferentCentralElements)

-- A left inverse on the selected original group is impossible.
selectedTransposeCannotHaveLeftInverse :
  (undo : Word.TritWord 13 → H.Heisenberg6) →
  ((g : H.Heisenberg6) →
    undo (selectedTransposeCode g) ≡ g) →
  ⊥
selectedTransposeCannotHaveLeftInverse undo invert =
  sourceCentralElementsDiffer
    (trans
      (sym (invert sourceCentralZero))
      (trans
        (cong undo selectedTransposeCollapsesDifferentCentralElements)
        (invert sourceCentralPositive)))

-- This is not a contradiction with invertibility of the
-- ORIGINAL 144-field transpose: its removed reverse relation
-- survives in the previously proved 131-cell residual.


------------------------------------------------------------------------
-- Positive repair of the original transpose information loss.
-- The central trit is moved into the (1,0) residual coordinate
-- after the 144-field transpose, exactly where the 13-code
-- projection loses it. No additional semantic group action
-- or external node is manufactured.
------------------------------------------------------------------------

selectedTransposeResidualAtReverse :
  (g : H.Heisenberg6) →
  Residual.maskUnobserved
    (Original.transposeRelation (Image.sourceGroupToOriginalRelation g))
    (Atlas.atlas-1 , Atlas.atlas-0)
  ≡ Rel.sourceCentralCoordinate (Bridge.originalGroupToSource g)
selectedTransposeResidualAtReverse g =
  Boundary.selectedRelationCentreRecovers
    (Bridge.originalGroupToSource g)

-- The full original 144-state records the moved centre without
-- information loss. The previously proven pointwise normal form
-- reopens it from the selected 13-code and retained 131 residual.
selectedTransposeReopensAtReverse :
  (g : H.Heisenberg6) →
  Residual.reopenNormalized
    (Boundary.relationToThirteen
      (Original.transposeRelation (Image.sourceGroupToOriginalRelation g)))
    (Residual.maskToResidual131
      (Original.transposeRelation (Image.sourceGroupToOriginalRelation g)))
    (Atlas.atlas-1 , Atlas.atlas-0)
  ≡ Rel.sourceCentralCoordinate (Bridge.originalGroupToSource g)
selectedTransposeReopensAtReverse g =
  trans
    (Residual.reopenNormalizedExact
      (Original.transposeRelation
        (Image.sourceGroupToOriginalRelation g))
      (Atlas.atlas-1 , Atlas.atlas-0))
    (Boundary.selectedRelationCentreRecovers
      (Bridge.originalGroupToSource g))
