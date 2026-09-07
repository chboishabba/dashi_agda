{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact where

------------------------------------------------------------------------
-- PATH13 SELECTED BACKGROUND: PHYSICAL DEFECT/ORDER REPRESENTATION EXTENSION
--
-- The selected variational bridge intentionally leaves its defect algebra and
-- order abstract.  The standard rational SU(2) operator representation is also
-- intentionally source-independent.  Eq. (119) needs a SAME-object statement
-- that the selected bridge uses that standard physical representation.
--
-- This extension owns exactly that identification.  It does not construct the
-- selected background, its native radius, or the standard operator
-- representation.  It also does not pay the scalar inclusion 1/24 <= r_cut;
-- that remains a separate selected-cut fact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
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

selectedPhysical :
  ∀ {CoarseField} →
  SelectedPath13OperatorChartRepresentation CoarseField →
  Target.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra
selectedPhysical representation =
  Fibre.selectedPhysical (backgroundRadius representation)

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

-- Same-object representation identification is still an inhabitant obligation;
-- this owner only gives it the correct dependent type.
literalCMP98Path13SelectedOperatorChartRepresentationLevel : ProofLevel
literalCMP98Path13SelectedOperatorChartRepresentationLevel = conditional
