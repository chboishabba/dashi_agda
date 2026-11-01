module DASHI.Physics.YangMills.BalabanUniformCanonicalSchurNormG2ClosureExact where

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
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- This is the physical-facing Round60 G2 compiler.  Round58 accepted four raw
-- upper endpoints plus sixteen independently supplied signed Green lower
-- endpoints.  Round60 proved
--
--   K+ >= 0
--     -> polarization
--     -> diagonal-energy lower bounds
--     -> Schur row-mass control of those energies.
--
-- Therefore the selected-region producer now supplies only
--
--   4 raw uppers
--   + 1 common K+ absolute-row bound
--   + 4 source degree-vector norm^2 uppers
--   + 4 defect degree-vector norm^2 uppers
--   + 1 positive charge floor
--   + the existing final rational endpoint comparison.
--
-- The sixteen signed Green endpoints are generated internally and fed into the
-- already-proved Round58 uniform selected-minimizer theorem.  The KKT data may
-- vary with configuration; only the rational endpoint bounds are shared.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as GreenSchur
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as SchurEnergy
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact as Uniform
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

record UniformCanonicalSchurNormG2Data
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    pseudoDataAt : Configuration →
      Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationAt : Configuration → KKT.StateVector
    bondFieldAt : Configuration → Physical.PhysicalSU2BondField4
    plaquetteAt : Configuration → Plaquette.Plaquette4

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        (pseudoDataAt configuration)
        (firstVariationAt configuration)
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    -- Four shared raw degree endpoints.
    rawUpper : Degree.MobiusDegree → ℚ
    rawSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ degree →
      CanonicalBlocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawUpper degree

    -- One shared Schur row endpoint for the literal configuration-dependent K+.
    rowBound : ℚ
    rowBoundNonnegative : 0ℚ ≤ rowBound
    rowsBoundedUniform : ∀ configuration →
      InCertifiedRegion configuration →
      SchurEnergy.pseudoinverseRowBound
        (pseudoDataAt configuration) rowBound

    -- Eight shared ordinary norm^2 endpoints.
    sourceNormUpper : Degree.MobiusDegree → ℚ
    defectNormUpper : Degree.MobiusDegree → ℚ

    sourceNormSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ degree →
      Rect.finiteNormSq
        (Pseudo.multiplierCarrier (pseudoDataAt configuration))
        (GreenDegree.sourceDegreeVector
          (Canonical.canonicalConstraintAtoms
            (canonicalInputsAt configuration)) degree)
      ≤ sourceNormUpper degree

    defectNormSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ degree →
      Rect.finiteNormSq
        (Pseudo.multiplierCarrier (pseudoDataAt configuration))
        (GreenDegree.defectDegreeVector
          (Canonical.canonicalConstraintAtoms
            (canonicalInputsAt configuration)) degree)
      ≤ defectNormUpper degree

    chargeAt : Configuration → ℚ
    chargeLower : ℚ
    chargeLowerBound : ∀ configuration →
      InCertifiedRegion configuration →
      chargeLower ≤ chargeAt configuration

open UniformCanonicalSchurNormG2Data public

canonicalSchurDataAt :
  ∀ {Configuration Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier)
    configuration →
  InCertifiedRegion dataSet configuration →
  GreenSchur.CanonicalGreenSchurNormData
    (canonicalInputsAt dataSet configuration)
canonicalSchurDataAt dataSet configuration inRegion = record
  { GreenSchur.CanonicalGreenSchurNormData.rowBound = rowBound dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.rowBoundNonnegative =
      rowBoundNonnegative dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.rowsBounded =
      rowsBoundedUniform dataSet configuration inRegion
  ; GreenSchur.CanonicalGreenSchurNormData.sourceNormUpper =
      sourceNormUpper dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.defectNormUpper =
      defectNormUpper dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.sourceNormSound =
      sourceNormSoundUniform dataSet configuration inRegion
  ; GreenSchur.CanonicalGreenSchurNormData.defectNormSound =
      defectNormSoundUniform dataSet configuration inRegion
  }

compiledGreenLower :
  ∀ {Configuration Multiplier} →
  UniformCanonicalSchurNormG2Data Configuration Multiplier →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
compiledGreenLower dataSet left right =
  - ((+ 1 / 2) *
      (GreenSchur.energyCoefficient (rowBound dataSet)
        * sourceNormUpper dataSet left
      + GreenSchur.energyCoefficient (rowBound dataSet)
        * defectNormUpper dataSet right))

compiledGreenLowerIsLocalSchurEndpoint :
  ∀ {Configuration Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    left right →
  compiledGreenLower dataSet left right
  ≡ GreenSchur.greenLowerFromSchurNorms
      (canonicalSchurDataAt dataSet configuration inRegion) left right
compiledGreenLowerIsLocalSchurEndpoint dataSet configuration inRegion left right = refl

compiledGreenSoundUniform :
  ∀ {Configuration Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier)
    configuration →
  InCertifiedRegion dataSet configuration →
  ∀ left right →
  compiledGreenLower dataSet left right
  ≤ CanonicalBlocks.canonicalGreenDegreeBlock
      (canonicalInputsAt dataSet configuration) left right
compiledGreenSoundUniform dataSet configuration inRegion left right =
  GreenSchur.greenLowerFromSchurNormsSound
    (canonicalSchurDataAt dataSet configuration inRegion) left right

asUniformSelectedMinimizerDegreeEnvelope :
  ∀ {Configuration Multiplier} →
  UniformCanonicalSchurNormG2Data Configuration Multiplier →
  Uniform.UniformSelectedMinimizerDegreeEnvelope Configuration
asUniformSelectedMinimizerDegreeEnvelope dataSet = record
  { Uniform.UniformSelectedMinimizerDegreeEnvelope.InCertifiedRegion =
      InCertifiedRegion dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.selectedMinimizer =
      selectedMinimizer dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.selectedMinimizerInRegion =
      selectedMinimizerInRegion dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.familyAt =
      λ configuration →
        CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration)
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeAt = chargeAt dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.rawUpper = rawUpper dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.greenLower =
      compiledGreenLower dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.rawSoundUniform =
      rawSoundUniform dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.greenSoundUniform =
      compiledGreenSoundUniform dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeLower =
      chargeLower dataSet
  ; Uniform.UniformSelectedMinimizerDegreeEnvelope.chargeLowerBound =
      chargeLowerBound dataSet
  }

record UniformCanonicalSchurNormG2Closure
    {Configuration Multiplier : Set}
    (dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier) : Set where
  field
    endpointFitsLowerCharge :
      Uniform.sharedResidualUpper
        (asUniformSelectedMinimizerDegreeEnvelope dataSet)
      ≤ Selector.remainingSingletonCoefficient * chargeLower dataSet
open UniformCanonicalSchurNormG2Closure public

asUniformDegreeClosure :
  ∀ {Configuration Multiplier}
    {dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier} →
  UniformCanonicalSchurNormG2Closure dataSet →
  Uniform.UniformSelectedMinimizerDegreeClosure
    (asUniformSelectedMinimizerDegreeEnvelope dataSet)
asUniformDegreeClosure closure = record
  { Uniform.UniformSelectedMinimizerDegreeClosure.uniformEndpointFitsLowerCharge =
      endpointFitsLowerCharge closure
  }

selectedMinimizerG2ClosesFromRowAndEightNorms :
  ∀ {Configuration Multiplier}
    (dataSet : UniformCanonicalSchurNormG2Data Configuration Multiplier)
    (closure : UniformCanonicalSchurNormG2Closure dataSet) →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerG2ClosesFromRowAndEightNorms dataSet closure =
  Uniform.selectedMinimizerCorrelatedResidualClosesFromSharedDegreeEndpoint
    (asUniformSelectedMinimizerDegreeEnvelope dataSet)
    (asUniformDegreeClosure closure)

uniformCanonicalSchurNormG2CompilerLevel : ProofLevel
uniformCanonicalSchurNormG2CompilerLevel = machineChecked

selectedMinimizerG2FromRowAndEightNormsLevel : ProofLevel
selectedMinimizerG2FromRowAndEightNormsLevel = machineChecked

-- Remaining G2 physical producer is now exactly the shared selected-region
-- numerical/analytic data in UniformCanonicalSchurNormG2Data plus the single
-- scalar endpoint comparison in UniformCanonicalSchurNormG2Closure.
selectedRegionCanonicalG2NumericalClosureLevel : ProofLevel
selectedRegionCanonicalG2NumericalClosureLevel = conditional
