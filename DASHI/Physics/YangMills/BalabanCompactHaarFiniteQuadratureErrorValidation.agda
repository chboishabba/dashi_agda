module DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Q

finiteQuadratureErrorCompilerOwned :
  Q.compactHaarFiniteQuadratureErrorLevel ≡ machineChecked
finiteQuadratureErrorCompilerOwned = refl

cellOscillationStillAnalytic :
  Q.literalProductHaarCellOscillationLevel ≡ conditional
cellOscillationStillAnalytic = refl

massDiscrepancyStillAnalytic :
  Q.literalProductHaarMassDiscrepancyLevel ≡ conditional
massDiscrepancyStillAnalytic = refl
