{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCylinderExpectationLimitMeasureValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCylinderExpectationLimitMeasureExact as A
limitAlgebraCompilerOwned : A.limitFunctionalAlgebraLevel ≡ machineChecked
limitAlgebraCompilerOwned = refl
measureRepresentationIsStandardAuthority :
  A.cylinderMeasureRepresentationAuthorityLevel ≡ standardImported
measureRepresentationIsStandardAuthority = refl
