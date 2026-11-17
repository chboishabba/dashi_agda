module DASHI.Physics.Closure.FactorVecFalsifiablePredictionLanes where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import MonsterOntos using (SSP; p31; toNat)
open import Ontology.GodelLattice using (FactorVec; Vec15)
open import Ontology.GodelScalarization using (G; primePower)

------------------------------------------------------------------------
-- Falsifiable prediction lanes over the 15SSP FactorVec carrier.
--
-- The point of this surface is not to assert that the lanes succeed.  It
-- fixes the no-fit protocol shape:
--
--   public data table -> FactorVec projection -> parameter-free prediction
--   -> chi-square/dof acceptance or rejection.
------------------------------------------------------------------------

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

infixr 2 _×_

open _×_ public

record Ratio : Set where
  constructor ratio
  field
    numerator   : Nat
    denominator : Nat

open Ratio public

one : Nat
one = suc zero

prime31Ratio : Ratio
prime31Ratio = ratio one (toNat p31)

record NoFreeParameters : Set where
  constructor noFreeParameters

------------------------------------------------------------------------
-- Shared chi-square protocol.
------------------------------------------------------------------------

record ChiSquaredProtocol : Set₁ where
  field
    Observable Prediction Uncertainty ChiSquared DOF : Set

    predicted : Observable → Prediction
    observed  : Observable → Prediction
    sigma     : Observable → Uncertainty

    χ²        : ChiSquared
    dof       : DOF
    χ²/dof≤2  : Set

    zeroFit   : NoFreeParameters

open ChiSquaredProtocol public

record PredictionLane : Set₁ where
  field
    Name : Set
    InputTable : Set
    protocol : ChiSquaredProtocol
    falsified : Set
    acceptedAtChi2Dof≤2 : χ²/dof≤2 protocol

open PredictionLane public

------------------------------------------------------------------------
-- Lane 1: Drell-Yan adjacent bin ratios.
------------------------------------------------------------------------

record DrellYanBinRatioLane : Set₁ where
  field
    Bin : Set

    -- Public HEPData/CMS/ATLAS table carrier.
    table : Set

    -- Fixed, pre-registered kinematic-to-carrier projection.
    binToFactorVec : Bin → FactorVec

    adjacent : Bin → Bin → Set

    -- Parameter-free SSP ratio:
    --   R_SSP(b,b') = G(v(b')) / G(v(b)).
    predictedAdjacentRatio :
      ∀ b b' → adjacent b b' → Ratio
    predictedAdjacentRatioLaw :
      ∀ b b' →
      (adj : adjacent b b') →
      predictedAdjacentRatio b b' adj ≡
        ratio (G (binToFactorVec b')) (G (binToFactorVec b))

    ObservedRatio Uncertainty ChiSquared DOF : Set
    observedAdjacentRatio :
      ∀ b b' → adjacent b b' → ObservedRatio
    ratioUncertainty :
      ∀ b b' → adjacent b b' → Uncertainty

    χ²       : ChiSquared
    dof      : DOF
    χ²/dof≤2 : Set

    zeroFit : NoFreeParameters

open DrellYanBinRatioLane public

drellYanPredictionProtocol :
  DrellYanBinRatioLane →
  Set
drellYanPredictionProtocol lane =
  ∀ b b' →
  (adj : adjacent lane b b') →
  predictedAdjacentRatio lane b b' adj ≡
    ratio (G (binToFactorVec lane b')) (G (binToFactorVec lane b))

------------------------------------------------------------------------
-- Lane 2: muon g-2 residual structure.
------------------------------------------------------------------------

record MuonGMinus2ResidualLane : Set₁ where
  field
    HadronicClass : Set
    MassScale Modulus Threshold : Set

    -- Carrier assignment for a hadronic correction class.
    classToFactorVec : HadronicClass → FactorVec

    -- Compression cost is a carrier-derived MDL code length.  Numeric logs
    -- are represented by the abstract Cost carrier so this stays independent
    -- of a particular real-number implementation.
    Cost : Set
    compressionCost : HadronicClass → Cost
    costFromFactorVec : HadronicClass → Set

    HVP HLBL QED EW : Set
    hvpResidualDominates : Set

    MDLExpensive : HadronicClass → Set
    residualContribution : HadronicClass → Set

    residualPrediction :
      ∀ α → MDLExpensive α → residualContribution α

    zeroFit : NoFreeParameters

open MuonGMinus2ResidualLane public

------------------------------------------------------------------------
-- Lane 3: neutrino mass/mixing discrete ratio.
------------------------------------------------------------------------

record NeutrinoMixingRatioLane : Set₁ where
  field
    MixingObservable ExperimentalWindow ErrorBound : Set

    pmnsToFactorVec : MixingObservable → FactorVec

    -- Sharp carrier prediction: Δm²21 / Δm²31 ≈ 1 / 31.
    predictedMassSplittingRatio : Ratio
    predictedMassSplittingRatioLaw :
      predictedMassSplittingRatio ≡ prime31Ratio

    discretizationError : ErrorBound
    landsInWindow : ExperimentalWindow → Set

    currentWindow : ExperimentalWindow
    predictionInCurrentWindow :
      landsInWindow currentWindow

    zeroFit : NoFreeParameters

open NeutrinoMixingRatioLane public

canonicalNeutrinoMassSplittingRatio :
  (lane : NeutrinoMixingRatioLane) →
  predictedMassSplittingRatio lane ≡ ratio one 31
canonicalNeutrinoMassSplittingRatio lane =
  predictedMassSplittingRatioLaw lane

------------------------------------------------------------------------
-- Lane 4: dark sector admissibility / exclusion bands.
------------------------------------------------------------------------

record DarkSectorAdmissibilityLane : Set₁ where
  field
    Candidate Coupling MassScale CarrierError : Set

    candidateToFactorVec : Candidate → FactorVec

    logMassRepresentable : Candidate → Set
    MDLAdmissible        : Candidate → Set
    MDLInadmissible      : Candidate → Set

    admissibleFromRepresentable :
      ∀ c → logMassRepresentable c → MDLAdmissible c

    excludedFromCarrierGap :
      ∀ c → MDLInadmissible c

    exclusionBand : CarrierError → Set
    largestSSPGapWitness : CarrierError
    highEndGapExclusion :
      exclusionBand largestSSPGapWitness

    zeroFit : NoFreeParameters

open DarkSectorAdmissibilityLane public

------------------------------------------------------------------------
-- Lane 5: Hubble / S8 projection-defect lane.
------------------------------------------------------------------------

record CosmologyProjectionDefectLane : Set₁ where
  field
    Measurement Embedding Defect Attractor : Set

    measurementToFactorVec : Measurement → FactorVec
    embedding : Measurement → Embedding
    projectionDefect : Measurement → Defect

    SameMDLAttractor : Measurement → Measurement → Attractor → Set
    NewEnergyComponentRequired : Measurement → Set

    tensionAsProjectionDefect :
      ∀ m₁ m₂ →
      Σ Attractor (λ A → SameMDLAttractor m₁ m₂ A)

    zeroFit : NoFreeParameters

open CosmologyProjectionDefectLane public

------------------------------------------------------------------------
-- Whole falsification program.
------------------------------------------------------------------------

record FactorVecFalsifiablePredictionProgram : Set₂ where
  field
    drellYan   : DrellYanBinRatioLane
    muonGMinus2 : MuonGMinus2ResidualLane
    neutrino   : NeutrinoMixingRatioLane
    darkSector : DarkSectorAdmissibilityLane
    cosmology  : CosmologyProjectionDefectLane

    unifiedProtocol : ChiSquaredProtocol

    -- Core claim shape:
    -- DASHI predicts observable ratios, exclusions, and residual signatures
    -- from F = Nat^15 with zero fitted parameters.
    ratiosExclusionsResidualsFromFactorVec : Set
    noFittedParameters :
      NoFreeParameters ×
      (NoFreeParameters ×
      (NoFreeParameters ×
      (NoFreeParameters ×
       NoFreeParameters)))

open FactorVecFalsifiablePredictionProgram public

allLaneZeroFit :
  (program : FactorVecFalsifiablePredictionProgram) →
  NoFreeParameters ×
  (NoFreeParameters ×
  (NoFreeParameters ×
  (NoFreeParameters ×
   NoFreeParameters)))
allLaneZeroFit program = noFittedParameters program
