module DASHI.Physics.YangMills.BalabanClayT5QuadratureStagedDiagonalTailValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5QuadratureStagedDiagonalTailExact as Q

triangleCompilerOwned :
  Q.quadratureFiniteContinuumTriangleLevel ≡ machineChecked
triangleCompilerOwned = refl

diagonalCauchyCompilerOwned :
  Q.quadratureStagedDiagonalCauchyLevel ≡ machineChecked
diagonalCauchyCompilerOwned = refl

diagonalConvergenceCompilerOwned :
  Q.quadratureStagedDiagonalConvergenceLevel ≡ machineChecked
diagonalConvergenceCompilerOwned = refl
