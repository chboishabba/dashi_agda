module DASHI.Physics.YangMills.BalabanClayT5AnisotropyPolymerSummationExact where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Perturbative methodological provenance.
--
-- Zohreh Davoudi and Martin J. Savage,
-- "Restoration of Rotational Symmetry in the Continuum Limit of Lattice Field
-- Theories", Physical Review D 86 (2012), 054505.
-- DOI: 10.1103/PhysRevD.86.054505; arXiv:1204.4146.
--
-- I. T. Drummond, A. Hart, R. R. Horgan, and L. C. Storoni,
-- "One Loop Calculation of the Renormalised Anisotropy for Improved
-- Anisotropic Gluon Actions on a Lattice", Physical Review D 66 (2002),
-- 094509. DOI: 10.1103/PhysRevD.66.094509; arXiv:hep-lat/0208010.
--
-- These are perturbative precedents only.  The exact theorem below is the finite
-- order-theoretic summation step.  The nonperturbative per-polymer O(a^2) bound
-- and a uniform summable majorant remain physical inputs.
------------------------------------------------------------------------

record AnisotropyPolymerSumData
    (Polymer Scale Bound : Set) : Set₁ where
  field
    polymers : List Polymer

    coefficientNorm majorant : Polymer → Scale → Bound
    latticeSpacingSquared : Scale → Bound

    zero : Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    perPolymerA2Bound : ∀ polymer scale →
      LessEqual
        (coefficientNorm polymer scale)
        (multiply (majorant polymer scale) (latticeSpacingSquared scale))

open AnisotropyPolymerSumData public

sumBy :
  ∀ {Polymer Scale Bound} →
  AnisotropyPolymerSumData Polymer Scale Bound →
  (Polymer → Bound) → List Polymer → Bound
sumBy dataSet term [] = zero dataSet
sumBy dataSet term (polymer ∷ rest) =
  add dataSet (term polymer) (sumBy dataSet term rest)

finiteAnisotropyBelowScaledMajorant :
  ∀ {Polymer Scale Bound}
    (dataSet : AnisotropyPolymerSumData Polymer Scale Bound)
    scale selected →
  LessEqual dataSet
    (sumBy dataSet (λ polymer → coefficientNorm dataSet polymer scale) selected)
    (sumBy dataSet
      (λ polymer → multiply dataSet
        (majorant dataSet polymer scale)
        (latticeSpacingSquared dataSet scale))
      selected)
finiteAnisotropyBelowScaledMajorant dataSet scale [] =
  reflexive dataSet (zero dataSet)
finiteAnisotropyBelowScaledMajorant dataSet scale (polymer ∷ rest) =
  addMonotone dataSet
    (perPolymerA2Bound dataSet polymer scale)
    (finiteAnisotropyBelowScaledMajorant dataSet scale rest)

record UniformAnisotropyMajorant
    {Polymer Scale Bound}
    (dataSet : AnisotropyPolymerSumData Polymer Scale Bound) : Set₁ where
  field
    totalAnisotropy totalA2Envelope : Scale → Bound

    totalAnisotropyBelowFiniteSum : ∀ scale →
      LessEqual dataSet
        (totalAnisotropy scale)
        (sumBy dataSet
          (λ polymer → coefficientNorm dataSet polymer scale)
          (polymers dataSet))

    scaledMajorantSumBelowEnvelope : ∀ scale →
      LessEqual dataSet
        (sumBy dataSet
          (λ polymer → multiply dataSet
            (majorant dataSet polymer scale)
            (latticeSpacingSquared dataSet scale))
          (polymers dataSet))
        (totalA2Envelope scale)

open UniformAnisotropyMajorant public

totalAnisotropyBelowA2Envelope :
  ∀ {Polymer Scale Bound}
    {dataSet : AnisotropyPolymerSumData Polymer Scale Bound} →
  (uniform : UniformAnisotropyMajorant dataSet) →
  ∀ scale →
  LessEqual dataSet
    (totalAnisotropy uniform scale)
    (totalA2Envelope uniform scale)
totalAnisotropyBelowA2Envelope {dataSet = dataSet} uniform scale =
  transitive dataSet
    (totalAnisotropyBelowFiniteSum uniform scale)
    (transitive dataSet
      (finiteAnisotropyBelowScaledMajorant dataSet scale (polymers dataSet))
      (scaledMajorantSumBelowEnvelope uniform scale))

record VanishingA2Envelope
    {Polymer Scale Bound}
    {dataSet : AnisotropyPolymerSumData Polymer Scale Bound}
    (uniform : UniformAnisotropyMajorant dataSet) : Set₁ where
  field
    ConvergesToZero : (Scale → Bound) → Set
    a2EnvelopeVanishes : ConvergesToZero (totalA2Envelope uniform)

open VanishingA2Envelope public

finiteAnisotropySummationLevel : ProofLevel
finiteAnisotropySummationLevel = machineChecked

totalAnisotropyA2EnvelopeAssemblyLevel : ProofLevel
totalAnisotropyA2EnvelopeAssemblyLevel = machineChecked

physicalPerPolymerAnisotropyA2InputsLevel : ProofLevel
physicalPerPolymerAnisotropyA2InputsLevel = conditional

physicalAnisotropyMajorantSummabilityInputsLevel : ProofLevel
physicalAnisotropyMajorantSummabilityInputsLevel = conditional

physicalA2EnvelopeContinuumMeaningInputsLevel : ProofLevel
physicalA2EnvelopeContinuumMeaningInputsLevel = conditional
