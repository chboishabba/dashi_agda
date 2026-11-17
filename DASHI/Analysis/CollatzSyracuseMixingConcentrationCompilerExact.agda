module DASHI.Analysis.CollatzSyracuseMixingConcentrationCompilerExact where

------------------------------------------------------------------------
-- THEOREM-BEARING CONCENTRATION HYPOTHESES
--
-- Spectral information alone never authorizes concentration.  A consumer must
-- supply either an explicit dependence coefficient theorem or the full
-- nonreversible pseudo-spectral-gap package it intends to use.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseCylinderCorrelationExact as Correlation

record MixingCoefficientSource : Set₁ where
  field
    correlationSource : Correlation.CylinderCorrelationSource
    alphaNumerator : Nat → Nat
    alphaDenominator : Nat
    alphaBound : (lag : Nat) → Set
    boundedParitySumConcentration :
      (length deviation : Nat) → Set

record PseudoSpectralGapSource : Set₁ where
  field
    level : Nat
    timeReversalDefined : Set
    multiplicativeReversibilizationDefined : Set
    pseudoSpectralGapPositive : Set
    boundedParityObservable : Set
    boundedParitySumConcentration :
      (length deviation : Nat) → Set

record SyracuseConcentrationSource : Set₁ where
  field
    parityConcentration : (length deviation : Nat) → Set
    producerIsTheoremBearing : Set

open SyracuseConcentrationSource public

record ConcentrationBoundary : Set where
  constructor concentrationBoundary
  field
    ordinaryEigenvalueGapAloneSuffices : Nat
    dependenceOrPseudoGapRequired : Nat
    boundedObservableRequired : Nat
    initialLawCorrectionMayBeNeeded : Nat

canonicalConcentrationBoundary : ConcentrationBoundary
canonicalConcentrationBoundary = concentrationBoundary 0 1 1 1
