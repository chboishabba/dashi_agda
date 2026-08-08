module DASHI.Papers.NavierStokes.ProjectorOperatorCoreRound27 where

------------------------------------------------------------------------
-- Paper-facing status for the Round 27 highest-alpha tranche.
--
-- Exact finite advances:
--
-- * sharp shell-projector idempotence, disjointness and finite resolution;
-- * Fourier reality as an involutive fixed-point condition;
-- * diagonal multiplier reality equivariance;
-- * separate state and multiplier/test carriers;
-- * signed translation--multiplier commutator identity;
-- * division-free centred five-source probe;
-- * maximal common viscosity-core theorem under unique ownership;
-- * physical resonant-triad Plucker/Gram geometry;
-- * reproducible finite certificate generation.
--
-- The full nonlinear vector-field equivariance, finite Picard--Lindelof,
-- physical shell evolution, cutoff-uniform taxes, periodic CZ estimate, strict
-- viscosity margin, limits and Clay theorem remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound27Exact as Round27

record ProjectorOperatorCoreRound27Status : Set where
  constructor projector-operator-core-round27-status
  field
    sharpFiniteShellProjectors : Bool
    realityInvolution : Bool
    diagonalRealityEquivariance : Bool
    stateDualSeparation : Bool
    signedTranslationMultiplierCommutator : Bool
    centredFiveSourceProbe : Bool
    maximalUniformViscosityCore : Bool
    physicalTriadPluckerGeometry : Bool
    finiteCertificatePipeline : Bool

    fullPhysicalVectorFieldEquivariance : Bool
    finitePicardLindelof : Bool
    physicalTimeDependentShellBalance : Bool
    cutoffUniformSignedOperatorTax : Bool
    cutoffUniformFiveClassTaxes : Bool
    periodicStrainCZTax : Bool
    strictTotalViscosityMargin : Bool
    shellAndGalerkinLimits : Bool
    unconditionalClayTheorem : Bool

open ProjectorOperatorCoreRound27Status public

canonicalProjectorOperatorCoreRound27Status :
  ProjectorOperatorCoreRound27Status
canonicalProjectorOperatorCoreRound27Status =
  projector-operator-core-round27-status
    true true true true true true true true true
    false false false false false false false false false

finiteProjectorOperatorCoreAdvanced :
  sharpFiniteShellProjectors canonicalProjectorOperatorCoreRound27Status
  ≡ true
finiteProjectorOperatorCoreAdvanced = refl

signedCommutatorAdvanced :
  signedTranslationMultiplierCommutator
    canonicalProjectorOperatorCoreRound27Status
  ≡ true
signedCommutatorAdvanced = refl

maximalCoreAdvanced :
  maximalUniformViscosityCore canonicalProjectorOperatorCoreRound27Status
  ≡ true
maximalCoreAdvanced = refl

physicalVectorFieldStillOpen :
  fullPhysicalVectorFieldEquivariance
    canonicalProjectorOperatorCoreRound27Status
  ≡ false
physicalVectorFieldStillOpen = refl

uniformOperatorTaxStillOpen :
  cutoffUniformSignedOperatorTax canonicalProjectorOperatorCoreRound27Status
  ≡ false
uniformOperatorTaxStillOpen = refl

strictMarginStillOpen :
  strictTotalViscosityMargin canonicalProjectorOperatorCoreRound27Status
  ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayTheorem canonicalProjectorOperatorCoreRound27Status
  ≡ false
clayPromotionStillFalse = refl

exactEvidence : Round27.Round27ExactEvidence
exactEvidence = Round27.canonicalRound27ExactEvidence
