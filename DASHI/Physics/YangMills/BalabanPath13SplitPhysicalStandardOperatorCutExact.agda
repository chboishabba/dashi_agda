{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SPLIT PHYSICAL VARIATIONAL DATA FROM STANDARD OPERATOR DATA
--
-- The previous preferred owner `SelectedPath13VariationalOperatorRepresentation`
-- bundled three conceptually different coordinates:
--
--   * selected Path13 variational/radius physics;
--   * R171's source-independent standard rational-SU(2) operator representation;
--   * the same-object equality between the selected cut defect and that
--     standard operator defect.
--
-- R171 itself marks its representation as `standardImported`, so it should not
-- be counted as part of the Path13 physical background producer.  This module
-- separates those fibres and leaves only the actual crossing equality as the
-- physical/representation weld.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale

record SplitPath13PhysicalStandardRepresentation
    (CoarseField : Set) : Set₁ where
  field
    physicalVariationalRadius :
      VariationalRadius.Path13SelectedVariationalRadiusRepresentation CoarseField

    standardOperatorRepresentation :
      R171.RationalSU2OperatorDefectRepresentation

    selectedCutDefectIsStandardOperatorDefect : ∀ value →
      Path.defect
        (Path.defectAlgebra
          (Selected.cutData
            (Target.bridge13
              (VariationalRadius.selected physicalVariationalRadius))))
        value
      ≡ Op.defect (R171.kernel standardOperatorRepresentation) value
open SplitPath13PhysicalStandardRepresentation public

selectedPhysical :
  ∀ {CoarseField} →
  SplitPath13PhysicalStandardRepresentation CoarseField →
  _
selectedPhysical inputs =
  VariationalRadius.selected (physicalVariationalRadius inputs)

selectedCutOrderIsRationalOrder :
  ∀ {CoarseField}
    (inputs : SplitPath13PhysicalStandardRepresentation CoarseField) →
  Scale.LessEqual
    (Path.scale
      (Path.defectAlgebra
        (Selected.cutData (Target.bridge13 (selectedPhysical inputs)))))
  ≡ _≤_
selectedCutOrderIsRationalOrder inputs =
  trans
    (cong
      (λ algebra → Scale.LessEqual (Path.scale algebra))
      (Selected.sameDefectAlgebra (Target.bridge13 (selectedPhysical inputs))))
    (VariationalRadius.selectedOrderIsRationalOrder
      (physicalVariationalRadius inputs))

cmp98Path13SplitPhysicalStandardRepresentationLevel : ProofLevel
cmp98Path13SplitPhysicalStandardRepresentationLevel = machineChecked

-- The R171 representation is source-independent standard authority.  The
-- remaining Path13-specific representation payment is only the selected-cut /
-- standard-operator same-object equality above.
literalCMP98Path13SelectedCutStandardOperatorWeldLevel : ProofLevel
literalCMP98Path13SelectedCutStandardOperatorWeldLevel = conditional
