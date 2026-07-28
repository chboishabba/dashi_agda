module DASHI.Physics.YangMills.BalabanClayT3PhysicalGreenCombesThomasExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto,
-- "Lattice Green Functions for Pedestrians: Exponential Decay",
-- Reviews in Mathematical Physics 36 (2024), article 2430005.
-- DOI: 10.1142/S0129055X2430005X; arXiv:2303.10754
-- Relationship: Theorem A / Theorem 2.25 gives an L-infinity Green estimate
-- uniform in lattice spacing and volume.  Its proof combines local
-- Combes--Thomas L2 decay, Fourier-strip analyticity, the RG identity and the
-- method of images.
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
--
-- Important source boundary: Dybalski--Stottmeister--Tanimoto explicitly omit
-- random-walk expansions.  They are therefore represented below as a separate
-- optional periodic/patch transfer authority, not as part of Combes--Thomas.
------------------------------------------------------------------------

record LocalCombesThomasBlockEstimate
    (Block State Scalar Operator Green : Set) : Set₂ where
  field
    blockDistance : Block → Block → Nat
    zero one : Scalar
    multiply subtract : Scalar → Scalar → Scalar
    exponential : Scalar → Scalar
    natScalar : Nat → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    operator : Operator
    green : Green
    spectralGap hoppingBound interactionRange decayRate l2Prefactor : Scalar

    supportedInBlock : State → Block → Set
    norm2 pairing : State → State → Scalar
    applyGreen : Green → State → State

    finiteRangeOperator : Set
    gaugeFixedSpectralGap : Set
    inverseOnGaugeFixedSpace : Set

    weightedConjugationDifferenceExact : ∀ centre → Set
    weightedPerturbationBound : ∀ centre → Set
    decayRatePositive : StrictLess zero decayRate
    perturbationBelowHalfGap : Set
    weightedNeumannResolventConverges : ∀ centre → Set
    weightedInverseNormBound : ∀ centre → Set

    localBlockL2Decay : ∀ left right leftState rightState →
      supportedInBlock leftState left →
      supportedInBlock rightState right →
      LessEqual
        (pairing rightState (applyGreen green leftState))
        (multiply l2Prefactor
          (multiply
            (exponential
              (subtract zero
                (multiply decayRate
                  (natScalar (blockDistance left right)))))
            (multiply (norm2 rightState rightState)
              (norm2 leftState leftState))))

open LocalCombesThomasBlockEstimate public

finiteRangeParametrixErrorBound = weightedPerturbationBound

record InfiniteLatticeFourierDecay
    (Scale Site Scalar Green Symbol : Set) : Set₂ where
  field
    distance : Site → Site → Nat
    zero one : Scalar
    multiply subtract : Scalar → Scalar → Scalar
    exponential : Scalar → Scalar
    natScalar : Nat → Scalar
    LessEqual : Scalar → Scalar → Set

    averagingGreen : Scale → Green
    FourierSymbol : Scale → Symbol
    stripWidth prefactor : Scalar

    FourierRepresentationExact : ∀ scale → Set
    FourierSymbolAnalyticInUniformStrip : ∀ scale → Set
    FourierSymbolBoundedInUniformStrip : ∀ scale → Set

    averagingKernel : Green → Site → Site → Scalar
    infiniteLatticeExponentialDecay : ∀ scale left right →
      LessEqual
        (averagingKernel (averagingGreen scale) left right)
        (multiply prefactor
          (exponential
            (subtract zero
              (multiply stripWidth
                (natScalar (distance left right))))))

open InfiniteLatticeFourierDecay public

record FiniteVolumeRGImageGreenDecay
    (Scale Volume Site Function Scalar Green : Set) : Set₂ where
  field
    zero one : Scalar
    add multiply subtract : Scalar → Scalar → Scalar
    exponential : Scalar → Scalar
    natScalar : Nat → Scalar
    LessEqual : Scalar → Scalar → Set

    distanceToSupport : Site → Function → Nat
    supNorm : Function → Scalar
    applyGreen : Green → Function → Site → Scalar

    finiteVolumeGreen fluctuationGreen : Scale → Volume → Green
    dimensionFactor prefactor decayRate : Scalar

    localCombesThomasInput : ∀ scale volume → Set
    infiniteLatticeFourierInput : ∀ scale → Set

    renormalizationGroupEquationExact : ∀ scale volume → Set
    methodOfImagesExact : ∀ scale volume → Set
    imageSumAbsolutelyConvergent : ∀ scale volume → Set
    imageTailExponential : ∀ scale volume → Set

    theoremAUniformSupNormDecay : ∀ scale volume function point →
      LessEqual
        (applyGreen (finiteVolumeGreen scale volume) function point)
        (multiply prefactor
          (multiply dimensionFactor
            (multiply
              (exponential
                (subtract zero
                  (multiply decayRate
                    (natScalar (distanceToSupport point function)))))
              (supNorm function))))

    fluctuationGreenFromRGDifferenceExact : ∀ scale volume → Set
    fluctuationGreenUniformSupNormDecay : ∀ scale volume function point →
      LessEqual
        (applyGreen (fluctuationGreen scale volume) function point)
        (multiply prefactor
          (multiply dimensionFactor
            (multiply
              (exponential
                (subtract zero
                  (multiply decayRate
                    (natScalar (distanceToSupport point function)))))
              (supNorm function))))

open FiniteVolumeRGImageGreenDecay public

physicalFluctuationGreenOffDiagonalDecayLiteral :
  ∀ {Scale Volume Site Function Scalar Green}
    (dataSet : FiniteVolumeRGImageGreenDecay
      Scale Volume Site Function Scalar Green)
    scale volume function point →
  LessEqual dataSet
    (applyGreen dataSet (fluctuationGreen dataSet scale volume) function point)
    (multiply dataSet (prefactor dataSet)
      (multiply dataSet (dimensionFactor dataSet)
        (multiply dataSet
          (exponential dataSet
            (subtract dataSet (zero dataSet)
              (multiply dataSet (decayRate dataSet)
                (natScalar dataSet
                  (distanceToSupport dataSet point function)))))
          (supNorm dataSet function))))
physicalFluctuationGreenOffDiagonalDecayLiteral =
  fluctuationGreenUniformSupNormDecay

patchUniformGreenDecay = physicalFluctuationGreenOffDiagonalDecayLiteral
scaleUniformGreenDecay = physicalFluctuationGreenOffDiagonalDecayLiteral
volumeUniformGreenDecay = physicalFluctuationGreenOffDiagonalDecayLiteral

record RandomWalkPeriodicPatchTransfer
    (Scale Volume Patch Green : Set) : Set₁ where
  field
    localGreen : Scale → Patch → Green
    periodicGreen : Scale → Volume → Green
    finiteRangeParametrixExact : ∀ scale patch → Set
    parametrixResidualStrictContraction : ∀ scale patch → Set
    randomWalkExpansionConverges : ∀ scale volume → Set
    periodicBoundaryTransferExact : ∀ scale volume → Set
    patchUniformDecayTransferred : ∀ scale volume → Set

open RandomWalkPeriodicPatchTransfer public

localCombesThomasReductionLevel : ProofLevel
localCombesThomasReductionLevel = machineChecked

fourierRGImageAssemblyLevel : ProofLevel
fourierRGImageAssemblyLevel = machineChecked

physicalFiniteRangeGapInputsLevel : ProofLevel
physicalFiniteRangeGapInputsLevel = conditional

physicalFourierRGImageInputsLevel : ProofLevel
physicalFourierRGImageInputsLevel = conditional

periodicRandomWalkTransferInputsLevel : ProofLevel
periodicRandomWalkTransferInputsLevel = conditional
