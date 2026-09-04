module DASHI.Physics.Catalysis.HighEntropyMBeneResidualScalingEscapeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualScalingLawEscapeExact as Scaling
import DASHI.Physics.Catalysis.HighEntropyMBeneMechanismHyperfabricExact as MBene

------------------------------------------------------------------------
-- HIGH-ENTROPY MBENE / RESIDUAL-SCALING BIDI BRIDGE
--
-- Physical source calibration:
-- Bharadwaj H and Ranganathan, npj Computational Materials (2026),
-- DOI 10.1038/s41524-026-02287-4.
--
-- The paper reports that high-entropy configurational disorder and local
-- Hf/Zr -> Cr charge donation stabilize COOH* and decouple linear scaling
-- relationships.  The generic DASHI theorem says what would be required for
-- an exact non-factorability statement: two physical states with the same
-- coarse adsorption chart but distinct residual/local coordinates and distinct
-- target energetics.
------------------------------------------------------------------------

record MBeneScalingChart : Set₁ where
  constructor mbene-scaling-chart
  field
    State CoarseAdsorptionCoordinate LocalElectronicResidual TargetIntermediateEnergy : Set
    coarseChartName residualChartName targetName : String

open MBeneScalingChart public

record MBeneResidualScalingProducer (chart : MBeneScalingChart) : Set₁ where
  constructor mbene-residual-scaling-producer
  field
    coarse : State chart → CoarseAdsorptionCoordinate chart
    residual : State chart → LocalElectronicResidual chart
    target : State chart → TargetIntermediateEnergy chart

    exactSeparatingWitness :
      Scaling.ResidualScalingWitness coarse residual target

open MBeneResidualScalingProducer public

exactMBeneResidualScalingBlocksCoarseDescent :
  ∀ {chart : MBeneScalingChart}
    (producer : MBeneResidualScalingProducer chart) →
  Scaling.ScalingLawDescends
    (coarse producer)
    (target producer) →
  ⊥
exactMBeneResidualScalingBlocksCoarseDescent producer =
  Scaling.residualScalingWitnessBlocksCoarseScalingLaw
    (exactSeparatingWitness producer)

exactMBeneResidualScalingGivesStrictRefinement :
  ∀ {chart : MBeneScalingChart}
    (producer : MBeneResidualScalingProducer chart) →
  _
exactMBeneResidualScalingGivesStrictRefinement producer =
  Scaling.residualScalingWitnessGivesStrictRefinement
    (exactSeparatingWitness producer)

------------------------------------------------------------------------
-- Source-backed mechanism receipt versus still-live exact witness.
--
-- The source supports the mechanism and LSR-decoupling claim, but this module
-- does not manufacture an exact pair of DFT configurations with literally
-- equal coarse coordinates.  That same-object numerical weld remains live.
------------------------------------------------------------------------

record SourceToExactScalingBoundary : Set where
  constructor source-to-exact-scaling-boundary
  field
    paperReportsLinearScalingDecoupling : Bool
    paperReportsLinearScalingDecouplingIsTrue :
      paperReportsLinearScalingDecoupling ≡ true

    paperReportsHfZrToCrChargeDonation : Bool
    paperReportsHfZrToCrChargeDonationIsTrue :
      paperReportsHfZrToCrChargeDonation ≡ true

    paperReportsCOOHStarStabilization : Bool
    paperReportsCOOHStarStabilizationIsTrue :
      paperReportsCOOHStarStabilization ≡ true

    exactEqualCoarseCoordinateSeparatingPairExtracted : Bool
    exactEqualCoarseCoordinateSeparatingPairExtractedIsFalse :
      exactEqualCoarseCoordinateSeparatingPairExtracted ≡ false

    sourceMechanismAloneProvesGenericNonFactorabilityWitness : Bool
    sourceMechanismAloneProvesGenericNonFactorabilityWitnessIsFalse :
      sourceMechanismAloneProvesGenericNonFactorabilityWitness ≡ false

canonicalSourceToExactScalingBoundary : SourceToExactScalingBoundary
canonicalSourceToExactScalingBoundary =
  source-to-exact-scaling-boundary
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Design-rule fibre extracted from the paper.  This is mechanistic guidance,
-- not an assertion that every composition satisfying it is experimentally
-- optimal.
------------------------------------------------------------------------

record ReportedDesignRule : Set where
  constructor reported-design-rule
  field
    donorRole : String
    activeSiteRole : String
    matrixRole : String
    desiredCO2Activation : String
    desiredCOOHStabilization : String
    desiredCODesorption : String

canonicalReportedDesignRule : ReportedDesignRule
canonicalReportedDesignRule = reported-design-rule
  "Hf or Zr electron donor"
  "Cr preferred adsorption centre"
  "Mo/Nb/Ta intermediate-field matrix"
  "balanced CO2 activation"
  "optimal COOH* stabilization"
  "facile CO* desorption"

------------------------------------------------------------------------
-- BIDI search contract.
--
-- Forward: physical local-state receipts produce residual coordinates and,
-- once an exact separating pair is available, a strict refinement / no-descent
-- theorem.
-- Reverse: a claimed scaling escape compiles back into the missing exact pair
-- obligation rather than being accepted from a performance scalar alone.
------------------------------------------------------------------------

record BidiScalingSearchContract : Set where
  constructor bidi-scaling-search-contract
  field
    forwardNeedsLocalElectronicResidual : Bool
    forwardNeedsLocalElectronicResidualIsTrue :
      forwardNeedsLocalElectronicResidual ≡ true

    forwardNeedsTargetIntermediateEnergy : Bool
    forwardNeedsTargetIntermediateEnergyIsTrue :
      forwardNeedsTargetIntermediateEnergy ≡ true

    reverseClaimRequiresEqualCoarseSeparatingPair : Bool
    reverseClaimRequiresEqualCoarseSeparatingPairIsTrue :
      reverseClaimRequiresEqualCoarseSeparatingPair ≡ true

    leaderboardScalarAloneDischargesScalingEscape : Bool
    leaderboardScalarAloneDischargesScalingEscapeIsFalse :
      leaderboardScalarAloneDischargesScalingEscape ≡ false

canonicalBidiScalingSearchContract : BidiScalingSearchContract
canonicalBidiScalingSearchContract =
  bidi-scaling-search-contract true refl true refl true refl false refl

------------------------------------------------------------------------
-- Cross-pollination statement kept explicit.
------------------------------------------------------------------------

record CrossPollinationStatus : Set where
  constructor cross-pollination-status
  field
    genericResidualScalingTheoremOwned : Bool
    genericResidualScalingTheoremOwnedIsTrue :
      genericResidualScalingTheoremOwned ≡ true

    sourceMechanismMappedToResidualCoordinates : Bool
    sourceMechanismMappedToResidualCoordinatesIsTrue :
      sourceMechanismMappedToResidualCoordinates ≡ true

    exactDFTSeparatingPairStillRequired : Bool
    exactDFTSeparatingPairStillRequiredIsTrue :
      exactDFTSeparatingPairStillRequired ≡ true

canonicalCrossPollinationStatus : CrossPollinationStatus
canonicalCrossPollinationStatus =
  cross-pollination-status true refl true refl true refl
