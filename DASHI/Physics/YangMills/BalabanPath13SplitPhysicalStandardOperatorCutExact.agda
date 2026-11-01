{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SPLIT PHYSICAL VARIATIONAL DATA FROM STANDARD OPERATOR DATA
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as Old
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

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
  Target.SelectedPhysicalBackground13Instantiation CoarseField Lie.SU2LieAlgebra
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

fromCombinedVariationalOperator :
  ∀ {CoarseField} →
  Old.SelectedPath13VariationalOperatorRepresentation CoarseField →
  SplitPath13PhysicalStandardRepresentation CoarseField
fromCombinedVariationalOperator old = record
  { SplitPath13PhysicalStandardRepresentation.physicalVariationalRadius =
      Old.variationalRadius old
  ; SplitPath13PhysicalStandardRepresentation.standardOperatorRepresentation =
      Old.operatorRepresentationFromVariational old
  ; SplitPath13PhysicalStandardRepresentation.selectedCutDefectIsStandardOperatorDefect =
      λ value →
        trans
          (cong
            (λ algebra → Path.defect algebra value)
            (Selected.sameDefectAlgebra
              (Target.bridge13
                (VariationalRadius.selected (Old.variationalRadius old)))))
          (Old.selectedDefectIsOperatorDefectFromVariational old value)
  }

cmp98Path13SplitPhysicalStandardRepresentationLevel : ProofLevel
cmp98Path13SplitPhysicalStandardRepresentationLevel = machineChecked

cmp98Path13CombinedRepresentationCompatibilityLevel : ProofLevel
cmp98Path13CombinedRepresentationCompatibilityLevel = machineChecked

literalCMP98Path13SelectedCutStandardOperatorWeldLevel : ProofLevel
literalCMP98Path13SelectedCutStandardOperatorWeldLevel = conditional
