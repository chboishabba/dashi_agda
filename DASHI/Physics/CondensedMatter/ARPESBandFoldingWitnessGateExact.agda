module DASHI.Physics.CondensedMatter.ARPESBandFoldingWitnessGateExact where

------------------------------------------------------------------------
-- GENERIC ARPES BAND-FOLDING WITNESS GATE
--
-- An ARPES source can report band folding without publishing a repository-
-- native total spectral-weight array.  This module separates:
--
--   (1) the type of an actual spectral observer;
--   (2) the exact witness required to prove a folded spectral pair;
--   (3) a source-status receipt saying the paper reports such folding.
--
-- No raw intensity values are invented.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact as Fe
import DASHI.Physics.CondensedMatter.HexagonalSqrt3R30ReciprocalFoldingExact as Hex
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

record SpectralObserver
    (Momentum Energy Intensity : Set) : Set₁ where
  constructor spectral-observer
  field
    intensity : Momentum -> Energy -> Intensity

open SpectralObserver public

record VisibilityClassifier (Intensity : Set) : Set₁ where
  constructor visibility-classifier
  field
    visible : Intensity -> Bool

open VisibilityClassifier public

record FoldedSpectralPairWitness
    {Momentum Energy Intensity : Set}
    (spectral : SpectralObserver Momentum Energy Intensity)
    (classifier : VisibilityClassifier Intensity)
    (foldClass : Momentum -> Torus.Residue3) : Set where
  constructor folded-spectral-pair-witness
  field
    originalMomentum foldedMomentum : Momentum
    selectedEnergy : Energy

    distinctMomentum :
      originalMomentum ≡ foldedMomentum -> ⊥

    sameFoldClass :
      foldClass originalMomentum ≡ foldClass foldedMomentum

    originalVisible :
      visible classifier
        (intensity spectral originalMomentum selectedEnergy)
      ≡ true

    foldedVisible :
      visible classifier
        (intensity spectral foldedMomentum selectedEnergy)
      ≡ true

open FoldedSpectralPairWitness public

record FlatBandNestingWitness
    {Momentum Energy Intensity : Set}
    (spectral : SpectralObserver Momentum Energy Intensity)
    (classifier : VisibilityClassifier Intensity) : Set where
  constructor flat-band-nesting-witness
  field
    firstMomentum secondMomentum : Momentum
    fermiEnergy : Energy

    firstVisible :
      visible classifier (intensity spectral firstMomentum fermiEnergy)
      ≡ true

    secondVisible :
      visible classifier (intensity spectral secondMomentum fermiEnergy)
      ≡ true

    distinctMomentum :
      firstMomentum ≡ secondMomentum -> ⊥

open FlatBandNestingWitness public

------------------------------------------------------------------------
-- Literal geometry adapter: the exact sqrt3 R30 fold-class producer can be
-- supplied directly to the generic witness type.
------------------------------------------------------------------------

literalSqrt3R30FoldClass :
  Torus.Torus3x3 -> Torus.Residue3
literalSqrt3R30FoldClass = Hex.foldClass

------------------------------------------------------------------------
-- Source status.  Reported observation != constructed repository witness.
------------------------------------------------------------------------

record Fe5GeTe2ARPESWitnessStatus : Set where
  constructor fe5gete2-arpes-witness-status
  field
    sourceReportsBandFolding : Bool
    sourceReportsFlatBandNestingVector : Bool
    sourceReportsLindhardSupport : Bool
    exactHexagonalFoldClassAvailable : Bool
    rawSpectralArrayAvailableInRepository : Bool
    foldedSpectralPairWitnessConstructed : Bool
    flatBandNestingWitnessConstructed : Bool
    lindhardFunctionRecomputedInKernel : Bool

canonicalFe5GeTe2ARPESWitnessStatus : Fe5GeTe2ARPESWitnessStatus
canonicalFe5GeTe2ARPESWitnessStatus =
  fe5gete2-arpes-witness-status
    true
    (Fe.flatBandNestingVectorReported Fe.canonicalFe5GeTe2SourceReplay)
    (Fe.lindhardResponseCalculationSupportsNestingInterpretation
      Fe.canonicalFe5GeTe2SourceReplay)
    true
    false
    false
    false
    false

record WitnessPromotionBoundary : Set where
  constructor witness-promotion-boundary
  field
    sourceReportAutomaticallyConstructsSpectralFunction : Bool
    symmetryLabelAutomaticallyConstructsIntensityArray : Bool
    exactFoldGeometryAutomaticallyProvesObservedIntensity : Bool
    rawDataOrEquivalentWitnessStillRequired : Bool

canonicalWitnessPromotionBoundary : WitnessPromotionBoundary
canonicalWitnessPromotionBoundary =
  witness-promotion-boundary
    false false false true
