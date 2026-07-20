module DASHI.Physics.YangMills.BalabanDashenGrossCalibration where

------------------------------------------------------------------------
-- Exact normalization ledger for the Dashen--Gross lattice/continuum coupling
-- map. Numerical constants are supplied separately; their composition and the
-- final calibration equation cannot drift silently.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.BalabanDashenGrossConventionMap
open import DASHI.Physics.YangMills.CompactLieProofLevel

record DashenGrossCalibrationData (Scalar : Set) : Set₁ where
  field
    multiply : Scalar → Scalar → Scalar
    balabanCoupling dashenGrossCoupling : Scalar
    generatorNormalization : Scalar
    latticeSpacingNormalization : Scalar
    determinantMultiplicity : Scalar

    conventionMap : Scalar → Scalar
    conventionDefinition : ∀ coupling →
      conventionMap coupling ≡
      multiply generatorNormalization
        (multiply latticeSpacingNormalization
          (multiply determinantMultiplicity coupling))

    calibratedProduct :
      multiply generatorNormalization
        (multiply latticeSpacingNormalization
          (multiply determinantMultiplicity balabanCoupling))
      ≡ dashenGrossCoupling

open DashenGrossCalibrationData public

calibratedConvention :
  ∀ {Scalar : Set} →
  (dataSet : DashenGrossCalibrationData Scalar) →
  conventionMap dataSet (balabanCoupling dataSet) ≡
  dashenGrossCoupling dataSet
calibratedConvention dataSet =
  trans
    (conventionDefinition dataSet (balabanCoupling dataSet))
    (calibratedProduct dataSet)

toDashenGrossConventionMap :
  ∀ {Scalar : Set} →
  DashenGrossCalibrationData Scalar → DashenGrossConventionMap Scalar
toDashenGrossConventionMap dataSet = record
  { balabanCoupling = balabanCoupling dataSet
  ; dashenGrossCoupling = dashenGrossCoupling dataSet
  ; generatorNormalization = generatorNormalization dataSet
  ; latticeSpacingNormalization = latticeSpacingNormalization dataSet
  ; determinantMultiplicity = determinantMultiplicity dataSet
  ; combine = multiply dataSet
  ; conventionMap = conventionMap dataSet
  ; calibrated = calibratedConvention dataSet
  }

dashenGrossCalibrationAssemblyLevel : ProofLevel
dashenGrossCalibrationAssemblyLevel = machineChecked

dashenGrossNumericalConstantsLevel : ProofLevel
dashenGrossNumericalConstantsLevel = standardImported
