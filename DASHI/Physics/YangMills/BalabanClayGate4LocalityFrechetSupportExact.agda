module DASHI.Physics.YangMills.BalabanClayGate4LocalityFrechetSupportExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact as CMP109
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact as Locality

------------------------------------------------------------------------
-- Local dependence implies structural derivative support.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The calculus fact used below is standard: the derivative of a constant curve
-- is zero.  The repository-specific input is that perturbing one fine bond does
-- not change any other fine-bond value.  If the selected bond lies outside the
-- endpoint support of a coarse bond, local dependence makes the coarse output
-- curve constant, hence its directional/Frechet kernel entry vanishes.
------------------------------------------------------------------------

record LocalCoordinateDerivativeMeaning
    (Input Output FineBond CoarseBond Value Parameter Entry : Set) : Set₁ where
  field
    locality : CMP109.ProjectedEndpointLocality
      Input Output FineBond CoarseBond Value

    perturbCoordinate : Input → FineBond → Parameter → Input
    zeroParameter : Parameter

    perturbAtZero : ∀ input fine →
      perturbCoordinate input fine zeroParameter ≡ input

    coordinatePerturbationPreservesOtherSites :
      ∀ input selected parameter other →
      selected ≡ other → Set

    coordinatePerturbationAgreesAwayFromSelected :
      ∀ input selected parameter other →
      CMP109.Not (selected ≡ other) →
      Locality.inputValue (CMP109.stage locality)
        (perturbCoordinate input selected parameter) other
      ≡ Locality.inputValue (CMP109.stage locality) input other

    derivativeEntry : Input → CoarseBond → FineBond → Entry
    zeroEntry : Entry

    CurveDerivative : (Parameter → Value) → Entry → Set

    derivativeEntryMeaning : ∀ input coarse fine →
      CurveDerivative
        (λ parameter →
          Locality.outputValue (CMP109.stage locality)
            (Locality.average (CMP109.stage locality)
              (perturbCoordinate input fine parameter))
            coarse)
        (derivativeEntry input coarse fine)

    constantCurveDerivativeZero :
      ∀ (curve : Parameter → Value) baseline derivative →
      (∀ parameter → curve parameter ≡ baseline) →
      CurveDerivative curve derivative →
      derivative ≡ zeroEntry

    supportExcludesSelectedFromOther :
      ∀ coarse selected other →
      CMP109.Not
        (CMP109.ProjectedEndpointSupport locality coarse selected) →
      CMP109.ProjectedEndpointSupport locality coarse other →
      CMP109.Not (selected ≡ other)

open LocalCoordinateDerivativeMeaning public

outsideCoordinateLeavesCoarseOutputConstant :
  ∀ {Input Output FineBond CoarseBond Value Parameter Entry}
    (meaning : LocalCoordinateDerivativeMeaning
      Input Output FineBond CoarseBond Value Parameter Entry)
    input coarse selected →
  CMP109.Not
    (CMP109.ProjectedEndpointSupport (locality meaning) coarse selected) →
  ∀ parameter →
  Locality.outputValue (CMP109.stage (locality meaning))
    (Locality.average (CMP109.stage (locality meaning))
      (perturbCoordinate meaning input selected parameter)) coarse
  ≡ Locality.outputValue (CMP109.stage (locality meaning))
      (Locality.average (CMP109.stage (locality meaning)) input) coarse
outsideCoordinateLeavesCoarseOutputConstant meaning input coarse selected
    selectedOutside parameter =
  CMP109.localDependenceOnProjectedEndpoints
    (locality meaning)
    (perturbCoordinate meaning input selected parameter)
    input coarse
    (λ other otherSupported →
      coordinatePerturbationAgreesAwayFromSelected meaning
        input selected parameter other
        (supportExcludesSelectedFromOther meaning
          coarse selected other selectedOutside otherSupported))

frechetEntryVanishesOutsideProjectedSupport :
  ∀ {Input Output FineBond CoarseBond Value Parameter Entry}
    (meaning : LocalCoordinateDerivativeMeaning
      Input Output FineBond CoarseBond Value Parameter Entry)
    input coarse selected →
  CMP109.Not
    (CMP109.ProjectedEndpointSupport (locality meaning) coarse selected) →
  derivativeEntry meaning input coarse selected ≡ zeroEntry meaning
frechetEntryVanishesOutsideProjectedSupport meaning input coarse selected
    selectedOutside =
  constantCurveDerivativeZero meaning
    (λ parameter →
      Locality.outputValue (CMP109.stage (locality meaning))
        (Locality.average (CMP109.stage (locality meaning))
          (perturbCoordinate meaning input selected parameter)) coarse)
    (Locality.outputValue (CMP109.stage (locality meaning))
      (Locality.average (CMP109.stage (locality meaning)) input) coarse)
    (derivativeEntry meaning input coarse selected)
    (outsideCoordinateLeavesCoarseOutputConstant meaning
      input coarse selected selectedOutside)
    (derivativeEntryMeaning meaning input coarse selected)

localityToConstantCoordinateCurveLevel : ProofLevel
localityToConstantCoordinateCurveLevel = machineChecked

constantCurveDerivativeSupportLevel : ProofLevel
constantCurveDerivativeSupportLevel = machineChecked

physicalCoordinatePerturbationMeaningInputsLevel : ProofLevel
physicalCoordinatePerturbationMeaningInputsLevel = conditional

physicalFrechetDerivativeMeaningInputsLevel : ProofLevel
physicalFrechetDerivativeMeaningInputsLevel = conditional
