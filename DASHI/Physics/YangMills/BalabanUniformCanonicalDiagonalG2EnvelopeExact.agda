module DASHI.Physics.YangMills.BalabanUniformCanonicalDiagonalG2EnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- This is the shortest current G2 endpoint carrier.  The old uniform theorem
-- accepted four raw upper endpoints plus SIXTEEN signed Green lower endpoints.
-- Round60 proved that the canonical KKT Gram pseudoinverse is PSD and that all
-- sixteen canonical Green degree blocks inherit polarization lower bounds from
-- only FOUR source and FOUR defect diagonal energies.
--
-- Therefore a physical selected-region producer now supplies only
--
--   4 raw upper bounds
-- + 4 source diagonal K+ energy upper bounds
-- + 4 defect diagonal K+ energy upper bounds
-- + 1 positive charge floor.
--
-- This module mechanically constructs the old 4+16 endpoint family and hence
-- reuses the existing selected-minimizer closure theorem.  No signed Green
-- endpoint remains an independent physical input.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalDegree
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact as Diagonal
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact as Uniform
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

record UniformCanonicalDiagonalG2Data
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (Configuration : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    firstVariationAt : Configuration → KKT.StateVector
    bondFieldAt : Configuration → Physical.PhysicalSU2BondField4
    plaquetteAt : Configuration → Flat.Plaquette4

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        pseudoData
        (firstVariationAt configuration)
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    chargeAt : Configuration → ℚ

    rawUpper : Degree.MobiusDegree → ℚ
    sourceEnergyUpper : Degree.MobiusDegree → ℚ
    defectEnergyUpper : Degree.MobiusDegree → ℚ

    rawUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      CanonicalDegree.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawUpper degree

    sourceEnergyUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      Diagonal.canonicalSourceDegreeEnergy
        (canonicalInputsAt configuration) degree
      ≤ sourceEnergyUpper degree

    defectEnergyUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      Diagonal.canonicalDefectDegreeEnergy
        (canonicalInputsAt configuration) degree
      ≤ defectEnergyUpper degree

    chargeLower : ℚ
    chargeLowerPositive : 0ℚ ≤ chargeLower
    chargeLowerSound : ∀ configuration →
      InCertifiedRegion configuration → chargeLower ≤ chargeAt configuration
open UniformCanonicalDiagonalG2Data public

generatedCanonicalGreenLower :
  ∀ {Multiplier Configuration pseudoData} →
  UniformCanonicalDiagonalG2Data {Multiplier} pseudoData Configuration →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
generatedCanonicalGreenLower dataSet sourceDegree defectDegree =
  half *
    (- (sourceEnergyUpper dataSet sourceDegree
      + defectEnergyUpper dataSet defectDegree))

generatedCanonicalGreenLowerSound :
  ∀ {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (dataSet : UniformCanonicalDiagonalG2Data pseudoData Configuration)
    configuration → InCertifiedRegion dataSet configuration →
    ∀ sourceDegree defectDegree →
  generatedCanonicalGreenLower dataSet sourceDegree defectDegree
  ≤ CanonicalDegree.canonicalGreenDegreeBlock
      (canonicalInputsAt dataSet configuration) sourceDegree defectDegree
generatedCanonicalGreenLowerSound
    dataSet configuration inRegion sourceDegree defectDegree =
  let
    inputs = canonicalInputsAt dataSet configuration
    sourceEnergy = Diagonal.canonicalSourceDegreeEnergy inputs sourceDegree
    defectEnergy = Diagonal.canonicalDefectDegreeEnergy inputs defectDegree
    sourceUpper = sourceEnergyUpper dataSet sourceDegree
    defectUpper = defectEnergyUpper dataSet defectDegree
    green = CanonicalDegree.canonicalGreenDegreeBlock inputs sourceDegree defectDegree

    energySumUpper :
      sourceEnergy + defectEnergy ≤ sourceUpper + defectUpper
    energySumUpper = ℚP.+-mono-≤
      (sourceEnergyUpperSound dataSet configuration inRegion sourceDegree)
      (defectEnergyUpperSound dataSet configuration inRegion defectDegree)

    negativeUpperBelowNegativeEnergy :
      - (sourceUpper + defectUpper) ≤ - (sourceEnergy + defectEnergy)
    negativeUpperBelowNegativeEnergy = ℚP.neg-antimono-≤ energySumUpper

    denominatorCleared :
      - (sourceUpper + defectUpper) ≤ green + green
    denominatorCleared = ℚP.≤-trans
      negativeUpperBelowNegativeEnergy
      (Diagonal.canonicalGreenDegreeLowerFromDiagonalEnergies
        inputs sourceDegree defectDegree)

    scaled :
      half * (- (sourceUpper + defectUpper)) ≤ half * (green + green)
    scaled = Norm.scaleNonnegative half
      (ℚP.nonNegative⁻¹ half) denominatorCleared
  in
  subst
    (λ upper → half * (- (sourceUpper + defectUpper)) ≤ upper)
    (ℚRing.solve-∀ green)
    scaled

compileCanonicalDiagonalToUniformDegreeEnvelope :
  ∀ {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier} →
  UniformCanonicalDiagonalG2Data pseudoData Configuration →
  Uniform.UniformSelectedMinimizerDegreeEnvelope Configuration
compileCanonicalDiagonalToUniformDegreeEnvelope dataSet = record
  { Uniform.UniformSelectedMinimizerDegreeEnvelope.InCertifiedRegion =
      InCertifiedRegion dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.selectedMinimizer =
      selectedMinimizer dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.selectedMinimizerInRegion =
      selectedMinimizerInRegion dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.familyAt =
      λ configuration →
        CanonicalDegree.canonicalFamily (canonicalInputsAt dataSet configuration)
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeAt = chargeAt dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.rawUpper = rawUpper dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.greenLower =
      generatedCanonicalGreenLower dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.rawSoundUniform =
      rawUpperSound dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.greenSoundUniform =
      generatedCanonicalGreenLowerSound dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeLower = chargeLower dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeLowerBound =
      chargeLowerSound dataSet
  }

record UniformCanonicalDiagonalG2Closure
    {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (dataSet : UniformCanonicalDiagonalG2Data pseudoData Configuration) : Set where
  field
    endpointFitsCharge :
      Uniform.sharedResidualUpper
        (compileCanonicalDiagonalToUniformDegreeEnvelope dataSet)
      ≤ Selector.remainingSingletonCoefficient * chargeLower dataSet
open UniformCanonicalDiagonalG2Closure public

canonicalDiagonalSelectedMinimizerG2Closure :
  ∀ {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (dataSet : UniformCanonicalDiagonalG2Data pseudoData Configuration)
    (closure : UniformCanonicalDiagonalG2Closure dataSet) →
  let compiled = compileCanonicalDiagonalToUniformDegreeEnvelope dataSet in
  DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact.correlatedResidualTotal
      (Uniform.familyAt compiled (Uniform.selectedMinimizer compiled))
  ≤ Selector.remainingSingletonCoefficient
      * Uniform.chargeAt compiled (Uniform.selectedMinimizer compiled)
canonicalDiagonalSelectedMinimizerG2Closure dataSet closure =
  Uniform.selectedMinimizerCorrelatedResidualClosesFromSharedDegreeEndpoint
    (compileCanonicalDiagonalToUniformDegreeEnvelope dataSet)
    (record { Uniform.UniformSelectedMinimizerDegreeClosure.uniformEndpointFitsLowerCharge =
      endpointFitsCharge closure })

uniformCanonicalDiagonalG2CompilerLevel : ProofLevel
uniformCanonicalDiagonalG2CompilerLevel = machineChecked

-- After this compiler the remaining G2 physical producer is exactly:
--   * four uniform raw upper bounds;
--   * eight uniform diagonal K+ energy upper bounds;
--   * one positive charge floor;
--   * one scalar endpoint comparison.
-- The first-variation source support and all sixteen signed Green lower boxes
-- are no longer independent obligations.
selectedRegionCanonicalFourPlusEightPlusChargeLevel : ProofLevel
selectedRegionCanonicalFourPlusEightPlusChargeLevel = conditional
