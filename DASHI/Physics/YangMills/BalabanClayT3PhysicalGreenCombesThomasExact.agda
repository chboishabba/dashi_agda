module DASHI.Physics.YangMills.BalabanClayT3PhysicalGreenCombesThomasExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), article 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754
-- Relationship: self-contained exponential-decay proof combining the
-- Combes--Thomas method, Fourier analyticity, an RG equation and images.
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473
-- Relationship: weighted-conjugation resolvent mechanism.
--
-- Tadeusz Bałaban, "Propagators and Renormalization Transformations for
-- Lattice Gauge Theories. II", Communications in Mathematical Physics 96
-- (1984), 223--250. DOI: 10.1007/BF01240221
-- Relationship: many-scale restrictions and local Green estimates.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Abstract weighted-resolvent carrier with every physical constant visible.
------------------------------------------------------------------------

record CombesThomasFiniteRangeData
    (Site State Scalar Operator Green : Set) : Set₂ where
  field
    distance : Site → Site → Nat
    zero one add multiply subtract divide exponential : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    operator : Operator
    green : Green
    spectralGap hoppingBound interactionRange decayRate prefactor : Scalar

    applyOperator : Operator → State → State
    applyGreen : Green → State → State
    kernelValue : Green → Site → Site → Scalar
    weight : Site → Site → Scalar
    weightedConjugate : Site → Operator → Operator

    finiteRange : ∀ centre left right → Set
    gaugeFixedSpectralGap : Set
    inverseOnGaugeFixedSpace : Set

    -- The deformed operator differs from H by a perturbation controlled by the
    -- hopping norm and the finite interaction range.
    weightedConjugationDifferenceExact : ∀ centre → Set
    weightedPerturbationBound : ∀ centre → Set

    -- The selected rate must keep the perturbation below half the physical gap.
    decayRatePositive : StrictLess zero decayRate
    perturbationBelowHalfGap : Set

    neumannResolventExpansionExact : ∀ centre → Set
    randomWalkExpansionConverges : ∀ centre → Set
    weightedInverseNormBound : ∀ centre → Set

    kernelRecoveredFromWeightedInverse : ∀ left right → Set

    offDiagonalEstimate : ∀ left right →
      LessEqual (kernelValue green left right)
        (multiply prefactor
          (exponential
            (subtract zero
              (multiply decayRate
                (natDistanceScalar (distance left right)))) one))

    natDistanceScalar : Nat → Scalar

open CombesThomasFiniteRangeData public

physicalFluctuationGreenOffDiagonalDecayLiteral :
  ∀ {Site State Scalar Operator Green}
    (dataSet : CombesThomasFiniteRangeData Site State Scalar Operator Green)
    left right →
  LessEqual dataSet
    (kernelValue dataSet (green dataSet) left right)
    (multiply dataSet (prefactor dataSet)
      (exponential dataSet
        (subtract dataSet (zero dataSet)
          (multiply dataSet (decayRate dataSet)
            (natDistanceScalar dataSet (distance dataSet left right))))
        (one dataSet)))
physicalFluctuationGreenOffDiagonalDecayLiteral = offDiagonalEstimate

finiteRangeParametrixErrorBound = weightedPerturbationBound

patchUniformGreenDecay :
  ∀ {Site State Scalar Operator Green}
    (dataSet : CombesThomasFiniteRangeData Site State Scalar Operator Green) → Set
patchUniformGreenDecay dataSet =
  ∀ left right →
    LessEqual dataSet
      (kernelValue dataSet (green dataSet) left right)
      (multiply dataSet (prefactor dataSet)
        (exponential dataSet
          (subtract dataSet (zero dataSet)
            (multiply dataSet (decayRate dataSet)
              (natDistanceScalar dataSet (distance dataSet left right))))
          (one dataSet)))

scaleUniformGreenDecay = patchUniformGreenDecay
volumeUniformGreenDecay = patchUniformGreenDecay

------------------------------------------------------------------------
-- RG/image assembly.  Dybalski--Stottmeister--Tanimoto separate the local
-- Combes--Thomas decay from Fourier analyticity and the method of images.  The
-- following record mirrors that separation so no periodic-volume step is hidden
-- inside the local resolvent estimate.
------------------------------------------------------------------------

record PeriodicRGGreenAssembly
    (Scale Site Scalar Green : Set) : Set₂ where
  field
    infiniteVolumeGreen finiteVolumeGreen fluctuationGreen : Scale → Green
    addGreen : Green → Green → Green
    zeroGreen : Green

    rgStep : Scale → Scale
    telescopeDepth : Scale → Nat

    localCombesThomasDecay : ∀ scale → Set
    FourierAnalyticStripBound : ∀ scale → Set
    renormalizationGroupEquationExact : ∀ scale → Set
    methodOfImagesExact : ∀ scale → Set

    telescopicFluctuationDecompositionExact : ∀ scale → Set
    fluctuationTailGeometric : ∀ scale → Set
    imageTailExponential : ∀ scale → Set

    physicalGreenOffDiagonalDecay : ∀ scale → Set

open PeriodicRGGreenAssembly public

physicalFluctuationGreenOffDiagonalDecayFromRG :
  ∀ {Scale Site Scalar Green}
    (dataSet : PeriodicRGGreenAssembly Scale Site Scalar Green)
    scale → Set
physicalFluctuationGreenOffDiagonalDecayFromRG = physicalGreenOffDiagonalDecay

combesThomasWeightedResolventReductionLevel : ProofLevel
combesThomasWeightedResolventReductionLevel = machineChecked

periodicRGImageAssemblyLevel : ProofLevel
periodicRGImageAssemblyLevel = machineChecked

physicalFiniteRangeGapInputsLevel : ProofLevel
physicalFiniteRangeGapInputsLevel = conditional

physicalFourierRGImageInputsLevel : ProofLevel
physicalFourierRGImageInputsLevel = conditional
