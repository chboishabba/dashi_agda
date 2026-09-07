{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR171OperatorKernelGroupDefectAdapterExact where

------------------------------------------------------------------------
-- R171 OPERATOR KERNEL -> GENERIC GROUP DEFECT ALGEBRA
--
-- `UnitaryOperatorDefectKernel` and `GroupDefectAlgebra` carry the same finite
-- multiplicative-defect content once the scalar is fixed to the rationals.
-- This adapter makes that identification literal instead of asking every
-- downstream Path13 consumer to prove a separate defect-function equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Operator

rationalOrderedAdditiveScale : Scale.OrderedAdditiveScale ℚ
rationalOrderedAdditiveScale = record
  { Scale.OrderedAdditiveScale.zeroScalar = 0ℚ
  ; Scale.OrderedAdditiveScale.add = _+_
  ; Scale.OrderedAdditiveScale.LessEqual = _≤_
  ; Scale.OrderedAdditiveScale.reflexive = λ value → ℚP.≤-refl
  ; Scale.OrderedAdditiveScale.transitive = ℚP.≤-trans
  ; Scale.OrderedAdditiveScale.addMonotone = ℚP.+-mono-≤
  }

operatorKernelAsGroupDefectAlgebra :
  ∀ {Group : Set} →
  Operator.UnitaryOperatorDefectKernel Group →
  Path.GroupDefectAlgebra Group ℚ
operatorKernelAsGroupDefectAlgebra kernel = record
  { Path.GroupDefectAlgebra.scale = rationalOrderedAdditiveScale
  ; Path.GroupDefectAlgebra.identity = Operator.identity kernel
  ; Path.GroupDefectAlgebra.multiply = Operator.multiply kernel
  ; Path.GroupDefectAlgebra.defect = Operator.defect kernel
  ; Path.GroupDefectAlgebra.defectIdentity = Operator.identityDefectZero kernel
  ; Path.GroupDefectAlgebra.defectProduct = Operator.productDefectTriangle kernel
  }

operatorDefectIsAdaptedGroupDefect :
  ∀ {Group : Set}
    (kernel : Operator.UnitaryOperatorDefectKernel Group)
    value →
  Path.defect (operatorKernelAsGroupDefectAlgebra kernel) value
  ≡ Operator.defect kernel value
operatorDefectIsAdaptedGroupDefect kernel value = refl

operatorKernelGroupDefectAdapterLevel : ProofLevel
operatorKernelGroupDefectAdapterLevel = machineChecked
