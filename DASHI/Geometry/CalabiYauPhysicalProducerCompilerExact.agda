module DASHI.Geometry.CalabiYauPhysicalProducerCompilerExact where

-- DASHI contribution: a typed constructor for the existing six-stage
-- physical compactification cutset.  Nothing here asserts that a concrete
-- CY3 vacuum has been obtained.  Every physical stage remains a supplied,
-- explicitly typed same-model witness.
--
-- Reuses CalabiYauPhysicalProducerCutset, not a parallel authority type.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)

import DASHI.Geometry.CalabiYauPhysicalProducerCutset as CY

record PhysicalProducerInputs (model : CY.ConcreteCompactCalabiYau) : Set₁ where
  field
    metric : CY.RicciFlatMetricAuthority model
    stabilized : CY.ModuliStabilizationAuthority model
    reduced : CY.DimensionalReductionAuthority model
    particles : CY.EffectiveSpectrumAuthority model
    interactions : CY.PhysicalCouplingAuthority model particles
    anomalies : CY.AnomalyCancellationAuthority model
    observational : CY.ObservationalPredictionAuthority model
    evidenceReceipt : String

open PhysicalProducerInputs public

compilePhysicalChain :
  (model : CY.ConcreteCompactCalabiYau) →
  PhysicalProducerInputs model →
  CY.PhysicalCompactificationChain
compilePhysicalChain model input = record
  { model = model
  ; ricciFlat = metric input
  ; stabilization = stabilized input
  ; reduction = reduced input
  ; spectrum = particles input
  ; couplings = interactions input
  ; anomalyCancellation = anomalies input
  ; predictionAuthority = observational input
  ; chainReceipt = evidenceReceipt input
  }

-- No implicit cross-model coercion: the same model indexes all six stages.
compilePreservesModel :
  (model : CY.ConcreteCompactCalabiYau) →
  (input : PhysicalProducerInputs model) →
  CY.PhysicalCompactificationChain.model
    (compilePhysicalChain model input) ≡ model
compilePreservesModel model input = refl

compilePreservesSpectrum :
  (model : CY.ConcreteCompactCalabiYau) →
  (input : PhysicalProducerInputs model) →
  CY.PhysicalCompactificationChain.spectrum
    (compilePhysicalChain model input) ≡ particles input
compilePreservesSpectrum model input = refl

-- The repository's existing non-promotion assertion is preserved.
structuralGeometryAloneDoesNotPayPhysicalModel :
  CY.CalabiYauPhysicalBoundary.dimensionIdentitySuppliesPhysicalModel
    CY.canonicalCalabiYauPhysicalBoundary ≡ false
structuralGeometryAloneDoesNotPayPhysicalModel = refl
