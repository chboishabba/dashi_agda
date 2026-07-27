module DASHI.Physics.YangMills.BalabanDashenGrossCalibration where

------------------------------------------------------------------------
-- Exact normalization ledger for the Dashen--Gross lattice/continuum coupling
-- map. Numerical constants are supplied separately; their composition and the
-- final calibration equation cannot drift silently.
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling",
-- Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340
--
-- The rational one-loop convention used by the Clay tranche is proved in
-- BalabanClayT4BetaNormalizationConventionExact.  In particular,
-- beta_0/(8 pi^2) with beta_0 = 11 C_A/3 is exactly
-- 11 C_A/(24 pi^2); the two notations are not competing coefficients.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.BalabanDashenGrossConventionMap
open import DASHI.Physics.YangMills.CompactLieProofLevel

record DashenGrossCalibrationData (Scalar : Set) : Set₁ where
  field
    multiplyFactor : Scalar → Scalar → Scalar
    sourceCoupling targetCoupling : Scalar
    generatorFactor : Scalar
    latticeFactor : Scalar
    determinantFactor : Scalar

    mapCoupling : Scalar → Scalar
    mapDefinition : ∀ coupling →
      mapCoupling coupling ≡
      multiplyFactor generatorFactor
        (multiplyFactor latticeFactor
          (multiplyFactor determinantFactor coupling))

    calibratedProduct :
      multiplyFactor generatorFactor
        (multiplyFactor latticeFactor
          (multiplyFactor determinantFactor sourceCoupling))
      ≡ targetCoupling

open DashenGrossCalibrationData public

calibratedConvention :
  ∀ {Scalar : Set} →
  (dataSet : DashenGrossCalibrationData Scalar) →
  mapCoupling dataSet (sourceCoupling dataSet) ≡ targetCoupling dataSet
calibratedConvention dataSet =
  trans
    (mapDefinition dataSet (sourceCoupling dataSet))
    (calibratedProduct dataSet)

toDashenGrossConventionMap :
  ∀ {Scalar : Set} →
  DashenGrossCalibrationData Scalar → DashenGrossConventionMap Scalar
toDashenGrossConventionMap dataSet = record
  { balabanCoupling = sourceCoupling dataSet
  ; dashenGrossCoupling = targetCoupling dataSet
  ; generatorNormalization = generatorFactor dataSet
  ; latticeSpacingNormalization = latticeFactor dataSet
  ; determinantMultiplicity = determinantFactor dataSet
  ; combine = multiplyFactor dataSet
  ; conventionMap = mapCoupling dataSet
  ; calibrated = calibratedConvention dataSet
  }

dashenGrossCalibrationAssemblyLevel : ProofLevel
dashenGrossCalibrationAssemblyLevel = machineChecked

dashenGrossBibliographicConventionLevel : ProofLevel
dashenGrossBibliographicConventionLevel = machineChecked

dashenGrossNumericalConstantsLevel : ProofLevel
dashenGrossNumericalConstantsLevel = standardImported
