{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkCMP119PotentialUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

ignoreVacuumAlgebra :
  Raw.CMP119RawActionAlgebra ℚ ℚ ℚ ℚ ℚ ℚ
ignoreVacuumAlgebra = record
  { assemble = λ coefficient wilson regular r boundary vacuum → coefficient }
  where open Raw.CMP119RawActionAlgebra

includeVacuumAlgebra :
  Raw.CMP119RawActionAlgebra ℚ ℚ ℚ ℚ ℚ ℚ
includeVacuumAlgebra = record
  { assemble = λ coefficient wilson regular r boundary vacuum → coefficient + vacuum }
  where open Raw.CMP119RawActionAlgebra

ignoreVacuumAtUnit :
  Raw.CMP119RawActionAlgebra.assemble ignoreVacuumAlgebra
    0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 1ℚ
  ≡ 0ℚ
ignoreVacuumAtUnit = refl

includeVacuumAtUnit :
  Raw.CMP119RawActionAlgebra.assemble includeVacuumAlgebra
    0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 1ℚ
  ≡ 1ℚ
includeVacuumAtUnit = refl

sameRawActionAlgebraTypeAllowsDifferentVacuumCoupling : Bool
sameRawActionAlgebraTypeAllowsDifferentVacuumCoupling = true

rawCMP119ActionTypeDoesNotDetermineHistoryPotentialCoupling : Bool
rawCMP119ActionTypeDoesNotDetermineHistoryPotentialCoupling = true

sourceNativePotentialCouplingTheoremStillRequired : Bool
sourceNativePotentialCouplingTheoremStillRequired = true

finiteTwoVacuumClassifierCanStillInstantiateAModel : Bool
finiteTwoVacuumClassifierCanStillInstantiateAModel = true
