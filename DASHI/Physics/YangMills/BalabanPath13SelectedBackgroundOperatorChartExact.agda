{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact where

------------------------------------------------------------------------
-- PATH13 SELECTED BACKGROUND: PHYSICAL DEFECT/ORDER REPRESENTATION EXTENSION
--
-- Compatibility consumers retain `SelectedPath13OperatorChartRepresentation`.
-- The preferred source-facing producer now starts from the stronger
-- variational-radius representation: rational order is reused from that owner
-- and the same-object radius fibre is generated mechanically.  Therefore the
-- only extra physical representation equality here is
--
--   selected defect = standard rational-SU(2) operator defect.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as Fibre
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record SelectedPath13OperatorChartRepresentation
    (CoarseField : Set) : Set₁ where
  field
    backgroundRadius : Fibre.SelectedPath13BackgroundWithRadius CoarseField

    operatorRepresentation : R171.RationalSU2OperatorDefectRepresentation

    selectedDefectIsOperatorDefect : ∀ value →
      Path.defect
        (Selected.defectAlgebra
          (Target.bridge13 (Fibre.selectedPhysical backgroundRadius)))
        value
      ≡ Op.defect (R171.kernel operatorRepresentation) value

    selectedOrderIsRationalOrder :
      Scale.LessEqual
        (Path.scale
          (Selected.defectAlgebra
            (Target.bridge13 (Fibre.selectedPhysical backgroundRadius))))
      ≡ _≤_

open SelectedPath13OperatorChartRepresentation public

------------------------------------------------------------------------
-- Preferred producer: radius and rational-order ownership come from the
-- variational-radius representation rather than being paid independently.
------------------------------------------------------------------------

record SelectedPath13VariationalOperatorRepresentation
    (CoarseField : Set) : Set₁ where
  field
    variationalRadius :
      VariationalRadius.Path13SelectedVariationalRadiusRepresentation CoarseField

    operatorRepresentationFromVariational :
      R171.RationalSU2OperatorDefectRepresentation

    selectedDefectIsOperatorDefectFromVariational : ∀ value →
      Path.defect
        (Selected.defectAlgebra
          (Target.bridge13
            (VariationalRadius.selected variationalRadius)))
        value
      ≡ Op.defect (R171.kernel operatorRepresentationFromVariational) value

open SelectedPath13VariationalOperatorRepresentation public

asSelectedPath13OperatorChartRepresentation :
  ∀ {CoarseField} →
  SelectedPath13VariationalOperatorRepresentation CoarseField →
  SelectedPath13OperatorChartRepresentation CoarseField
asSelectedPath13OperatorChartRepresentation inputs = record
  { backgroundRadius =
      Fibre.fromSelectedVariationalRadius (variationalRadius inputs)
  ; operatorRepresentation = operatorRepresentationFromVariational inputs
  ; selectedDefectIsOperatorDefect =
      selectedDefectIsOperatorDefectFromVariational inputs
  ; selectedOrderIsRationalOrder =
      VariationalRadius.selectedOrderIsRationalOrder
        (variationalRadius inputs)
  }

selectedPhysical :
  ∀ {CoarseField} →
  SelectedPath13OperatorChartRepresentation CoarseField →
  Target.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra
selectedPhysical representation =
  Fibre.selectedPhysical (backgroundRadius representation)

preferredSelectedPhysical :
  ∀ {CoarseField} →
  SelectedPath13VariationalOperatorRepresentation CoarseField →
  Target.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra
preferredSelectedPhysical inputs =
  VariationalRadius.selected (variationalRadius inputs)

preferredSelectedPhysicalExact :
  ∀ {CoarseField}
    (inputs : SelectedPath13VariationalOperatorRepresentation CoarseField) →
  selectedPhysical (asSelectedPath13OperatorChartRepresentation inputs)
  ≡ preferredSelectedPhysical inputs
preferredSelectedPhysicalExact inputs = Agda.Builtin.Equality.refl

selectedCutDefectIsOperatorDefect :
  ∀ {CoarseField}
    (representation : SelectedPath13OperatorChartRepresentation CoarseField)
    value →
  Path.defect
    (Path.defectAlgebra
      (Selected.cutData (Target.bridge13 (selectedPhysical representation))))
    value
  ≡ Op.defect (R171.kernel (operatorRepresentation representation)) value
selectedCutDefectIsOperatorDefect representation value =
  trans
    (cong
      (λ algebra → Path.defect algebra value)
      (Selected.sameDefectAlgebra
        (Target.bridge13 (selectedPhysical representation))))
    (selectedDefectIsOperatorDefect representation value)

selectedCutOrderIsRationalOrder :
  ∀ {CoarseField}
    (representation : SelectedPath13OperatorChartRepresentation CoarseField) →
  Scale.LessEqual
    (Path.scale
      (Path.defectAlgebra
        (Selected.cutData (Target.bridge13 (selectedPhysical representation)))))
  ≡ _≤_
selectedCutOrderIsRationalOrder representation =
  trans
    (cong
      (λ algebra → Scale.LessEqual (Path.scale algebra))
      (Selected.sameDefectAlgebra
        (Target.bridge13 (selectedPhysical representation))))
    (selectedOrderIsRationalOrder representation)

cmp98Path13SelectedOperatorChartRepresentationLevel : ProofLevel
cmp98Path13SelectedOperatorChartRepresentationLevel = machineChecked

cmp98Path13VariationalOperatorRepresentationCompilerLevel : ProofLevel
cmp98Path13VariationalOperatorRepresentationCompilerLevel = machineChecked

-- The compatibility owner remains conditional.  On the preferred route the
-- radius and order are compiler outputs; the remaining new representation
-- payment is the selected-defect/operator-defect same-object identification.
literalCMP98Path13SelectedOperatorChartRepresentationLevel : ProofLevel
literalCMP98Path13SelectedOperatorChartRepresentationLevel = conditional
