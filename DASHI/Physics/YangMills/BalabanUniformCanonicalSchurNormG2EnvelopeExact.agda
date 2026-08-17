module DASHI.Physics.YangMills.BalabanUniformCanonicalSchurNormG2EnvelopeExact where

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
-- Issai Schur, classical finite matrix norm test (1911), no DOI.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Round60 first reduced sixteen signed Green lower bounds to eight diagonal
-- K+ energies and then proved each diagonal energy is bounded by
--
--   (1/2) (1 + B^2) ||v||^2
--
-- from ONE common Schur row-mass bound B for the same symmetric K+.
-- This file eliminates the intermediate eight energy endpoints from the
-- physical G2 interface.  A selected-region producer now gives directly:
--
--   4 raw upper bounds
-- + 1 common K+ row-mass/Schur certificate
-- + 4 source-degree norm-square bounds
-- + 4 defect-degree norm-square bounds
-- + 1 positive charge floor
-- + the final scalar endpoint comparison.
--
-- The compiler constructs the exact diagonal-energy endpoints and then reuses
-- the canonical 4+8 -> 4+16 -> selected-minimizer theorem chain.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as Energy
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as NormReduction
import DASHI.Physics.YangMills.BalabanUniformCanonicalDiagonalG2EnvelopeExact as DiagonalEnvelope
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact as Uniform
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

record UniformCanonicalSchurNormG2Data
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
    rawUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawUpper degree

    schur : Energy.PseudoinverseSchurBound pseudoData

    sourceNormUpper : Degree.MobiusDegree → ℚ
    defectNormUpper : Degree.MobiusDegree → ℚ

    sourceNormUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      NormReduction.canonicalSourceDegreeNormSq
        (canonicalInputsAt configuration) degree
      ≤ sourceNormUpper degree

    defectNormUpperSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      NormReduction.canonicalDefectDegreeNormSq
        (canonicalInputsAt configuration) degree
      ≤ defectNormUpper degree

    chargeLower : ℚ
    chargeLowerPositive : 0ℚ ≤ chargeLower
    chargeLowerSound : ∀ configuration →
      InCertifiedRegion configuration → chargeLower ≤ chargeAt configuration
open UniformCanonicalSchurNormG2Data public

compileSchurNormToDiagonalG2 :
  ∀ {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier} →
  UniformCanonicalSchurNormG2Data pseudoData Configuration →
  DiagonalEnvelope.UniformCanonicalDiagonalG2Data pseudoData Configuration
compileSchurNormToDiagonalG2 dataSet = record
  { DiagonalEnvelope.UniformCanonicalDiagonalG2Data.InCertifiedRegion =
      InCertifiedRegion dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.selectedMinimizer =
      selectedMinimizer dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.selectedMinimizerInRegion =
      selectedMinimizerInRegion dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.firstVariationAt =
      firstVariationAt dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.bondFieldAt =
      bondFieldAt dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.plaquetteAt =
      plaquetteAt dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.canonicalInputsAt =
      canonicalInputsAt dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.chargeAt = chargeAt dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.rawUpper = rawUpper dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.sourceEnergyUpper =
      λ degree → NormReduction.derivedEnergyUpper
        (schur dataSet) (sourceNormUpper dataSet degree)
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.defectEnergyUpper =
      λ degree → NormReduction.derivedEnergyUpper
        (schur dataSet) (defectNormUpper dataSet degree)
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.rawUpperSound =
      rawUpperSound dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.sourceEnergyUpperSound =
      λ configuration inRegion degree →
        NormReduction.canonicalSourceEnergyUpperFromNorm
          (schur dataSet)
          (canonicalInputsAt dataSet configuration)
          degree
          (sourceNormUpper dataSet degree)
          (sourceNormUpperSound dataSet configuration inRegion degree)
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.defectEnergyUpperSound =
      λ configuration inRegion degree →
        NormReduction.canonicalDefectEnergyUpperFromNorm
          (schur dataSet)
          (canonicalInputsAt dataSet configuration)
          degree
          (defectNormUpper dataSet degree)
          (defectNormUpperSound dataSet configuration inRegion degree)
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.chargeLower = chargeLower dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.chargeLowerPositive =
      chargeLowerPositive dataSet
  ; DiagonalEnvelope.UniformCanonicalDiagonalG2Data.chargeLowerSound =
      chargeLowerSound dataSet
  }

record UniformCanonicalSchurNormG2Closure
    {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data pseudoData Configuration) : Set where
  field
    endpointFitsCharge :
      Uniform.sharedResidualUpper
        (DiagonalEnvelope.compileCanonicalDiagonalToUniformDegreeEnvelope
          (compileSchurNormToDiagonalG2 dataSet))
      ≤ Selector.remainingSingletonCoefficient * chargeLower dataSet
open UniformCanonicalSchurNormG2Closure public

canonicalSchurNormSelectedMinimizerG2Closure :
  ∀ {Multiplier Configuration}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data pseudoData Configuration)
    (closure : UniformCanonicalSchurNormG2Closure dataSet) →
  let diagonal = compileSchurNormToDiagonalG2 dataSet
      compiled = DiagonalEnvelope.compileCanonicalDiagonalToUniformDegreeEnvelope diagonal
  in
  Ownership.correlatedResidualTotal
      (Uniform.familyAt compiled (Uniform.selectedMinimizer compiled))
  ≤ Selector.remainingSingletonCoefficient
      * Uniform.chargeAt compiled (Uniform.selectedMinimizer compiled)
canonicalSchurNormSelectedMinimizerG2Closure dataSet closure =
  DiagonalEnvelope.canonicalDiagonalSelectedMinimizerG2Closure
    (compileSchurNormToDiagonalG2 dataSet)
    (record
      { DiagonalEnvelope.UniformCanonicalDiagonalG2Closure.endpointFitsCharge =
          endpointFitsCharge closure })

uniformCanonicalSchurNormG2CompilerLevel : ProofLevel
uniformCanonicalSchurNormG2CompilerLevel = machineChecked

-- Physical frontier after this exact compiler:
--   four raw upper endpoints;
--   one common row-mass bound for the literal K+;
--   four source and four defect degree-vector norm-square endpoints;
--   one positive charge floor;
--   one final scalar endpoint comparison.
selectedRegionCanonicalSchurNormG2PhysicalLevel : ProofLevel
selectedRegionCanonicalSchurNormG2PhysicalLevel = conditional
