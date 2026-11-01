module DASHI.Physics.YangMills.BalabanClaySpectralUVCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories", Physical Review
-- Letters 30 (1973), 1343--1346. DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?", Physical Review
-- Letters 30 (1973), 1346--1349. DOI: 10.1103/PhysRevLett.30.1346.
--
-- DASHI CONTRIBUTION
--
-- The mass gap is an infrared support statement for gauge-invariant spectral
-- measures.  Asymptotic freedom is a ultraviolet statement about renormalized
-- short-distance amplitudes.  They are not negations of one another.  A real
-- construction must nevertheless supply one observable-level compatibility
-- package joining the subtracted spectral representation to the RG/OPE row.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SpectralUVCompatibilityData
    (Observable SpectralMeasure Momentum Amplitude : Set) : Set₁ where
  field
    spectralMeasure : Observable → SpectralMeasure
    momentumAmplitude : Observable → Momentum → Amplitude

    PositiveMassThreshold : SpectralMeasure → Set
    SubtractedDispersionRepresentation :
      SpectralMeasure → (Momentum → Amplitude) → Set
    RGUltravioletAsymptotic :
      Observable → (Momentum → Amplitude) → Set

    spectralThreshold : ∀ observable →
      PositiveMassThreshold (spectralMeasure observable)
    dispersionRepresentation : ∀ observable →
      SubtractedDispersionRepresentation
        (spectralMeasure observable)
        (momentumAmplitude observable)
    ultravioletAsymptotic : ∀ observable →
      RGUltravioletAsymptotic observable
        (momentumAmplitude observable)

open SpectralUVCompatibilityData public

record SpectralUVCompatibility
    {Observable SpectralMeasure Momentum Amplitude : Set}
    (dataSet : SpectralUVCompatibilityData
      Observable SpectralMeasure Momentum Amplitude) : Set₁ where
  field
    positiveInfraredThreshold : ∀ observable →
      PositiveMassThreshold dataSet (spectralMeasure dataSet observable)
    commonSubtractedAmplitude : ∀ observable →
      SubtractedDispersionRepresentation dataSet
        (spectralMeasure dataSet observable)
        (momentumAmplitude dataSet observable)
    ultravioletRGMeaning : ∀ observable →
      RGUltravioletAsymptotic dataSet observable
        (momentumAmplitude dataSet observable)

open SpectralUVCompatibility public

assembleSpectralUVCompatibility :
  ∀ {Observable SpectralMeasure Momentum Amplitude}
    (dataSet : SpectralUVCompatibilityData
      Observable SpectralMeasure Momentum Amplitude) →
  SpectralUVCompatibility dataSet
assembleSpectralUVCompatibility dataSet = record
  { positiveInfraredThreshold = spectralThreshold dataSet
  ; commonSubtractedAmplitude = dispersionRepresentation dataSet
  ; ultravioletRGMeaning = ultravioletAsymptotic dataSet
  }

spectralUVCompatibilityAssemblyLevel : ProofLevel
spectralUVCompatibilityAssemblyLevel = machineChecked

physicalSpectralUVInputsLevel : ProofLevel
physicalSpectralUVInputsLevel = conditional
