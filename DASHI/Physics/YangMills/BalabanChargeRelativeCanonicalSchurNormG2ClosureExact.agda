module DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalSchurNormG2ClosureExact where

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
-- The companion zero-field theorem proves that the literal Wilson cross charge
-- vanishes on the zero variation, so an unconditional positive absolute charge
-- floor is the wrong homogeneous target.  This module removes it completely.
--
-- A selected-region proof instead supplies dimensionless coefficient bounds
-- relative to the ACTUAL nonnegative charge Q(A):
--
--   R_d(A)            <= r_d Q(A),
--   ||S_d(A)||^2      <= s_d Q(A),
--   ||D_d(A)||^2      <= t_d Q(A),
--   rowMass(K+(A))    <= B.
--
-- The Round60 PSD/polarization/Schur chain then gives all sixteen Green lower
-- bounds with the same factor Q(A).  Finite-sum algebra factors Q(A) out of the
-- whole residual and reduces the physical closure to ONE coefficient gate
--
--   residualRatio <= 55 / 18874368.
--
-- No division by Q and no Q>0 premise occurs.  The zero-charge branch closes
-- automatically by homogeneity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact as Interval
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as GreenSchur
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as SchurEnergy
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ChargeRelativeCanonicalG2Data
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

    chargeAt : Configuration → ℚ
    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration → 0ℚ ≤ chargeAt configuration

    -- Shared dimensionless physical coefficients.
    rawRatio : Degree.MobiusDegree → ℚ
    sourceNormRatio : Degree.MobiusDegree → ℚ
    defectNormRatio : Degree.MobiusDegree → ℚ

    rawRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      CanonicalBlocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawRatio degree * chargeAt configuration

    sourceNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      Rect.finiteNormSq
        (Pseudo.multiplierCarrier (pseudoDataAt configuration))
        (GreenDegree.sourceDegreeVector
          (Canonical.canonicalConstraintAtoms
            (canonicalInputsAt configuration)) degree)
      ≤ sourceNormRatio degree * chargeAt configuration

    defectNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      Rect.finiteNormSq
        (Pseudo.multiplierCarrier (pseudoDataAt configuration))
        (GreenDegree.defectDegreeVector
          (Canonical.canonicalConstraintAtoms
            (canonicalInputsAt configuration)) degree)
      ≤ defectNormRatio degree * chargeAt configuration

    rowBound : ℚ
    rowBoundNonnegative : 0ℚ ≤ rowBound
    rowsBoundedUniform : ∀ configuration →
      InCertifiedRegion configuration →
      SchurEnergy.pseudoinverseRowBound
        (pseudoDataAt configuration) rowBound

open ChargeRelativeCanonicalG2Data public

localSchurData :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  GreenSchur.CanonicalGreenSchurNormData
    (canonicalInputsAt dataSet configuration)
localSchurData dataSet configuration inRegion = record
  { GreenSchur.CanonicalGreenSchurNormData.rowBound = rowBound dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.rowBoundNonnegative =
      rowBoundNonnegative dataSet
  ; GreenSchur.CanonicalGreenSchurNormData.rowsBounded =
      rowsBoundedUniform dataSet configuration inRegion
  ; GreenSchur.CanonicalGreenSchurNormData.sourceNormUpper =
      λ degree → sourceNormRatio dataSet degree * chargeAt dataSet configuration
  ; GreenSchur.CanonicalGreenSchurNormData.defectNormUpper =
      λ degree → defectNormRatio dataSet degree * chargeAt dataSet configuration
  ; GreenSchur.CanonicalGreenSchurNormData.sourceNormSound =
      sourceNormRelativeSound dataSet configuration inRegion
  ; GreenSchur.CanonicalGreenSchurNormData.defectNormSound =
      defectNormRelativeSound dataSet configuration inRegion
  }

relativeGreenRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
relativeGreenRatio dataSet left right =
  - ((+ 1 / 2) *
      (GreenSchur.energyCoefficient (rowBound dataSet)
        * sourceNormRatio dataSet left
      + GreenSchur.energyCoefficient (rowBound dataSet)
        * defectNormRatio dataSet right))

relativeGreenEndpoint :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier →
  Configuration → Degree.MobiusDegree → Degree.MobiusDegree → ℚ
relativeGreenEndpoint dataSet configuration left right =
  relativeGreenRatio dataSet left right * chargeAt dataSet configuration

relativeGreenEndpointIsSchurEndpoint :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    left right →
  relativeGreenEndpoint dataSet configuration left right
  ≡ GreenSchur.greenLowerFromSchurNorms
      (localSchurData dataSet configuration inRegion) left right
relativeGreenEndpointIsSchurEndpoint dataSet configuration inRegion left right =
  ℚRing.solve-∀
    (GreenSchur.energyCoefficient (rowBound dataSet))
    (sourceNormRatio dataSet left)
    (defectNormRatio dataSet right)
    (chargeAt dataSet configuration)

relativeGreenSound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
    ∀ left right →
  relativeGreenEndpoint dataSet configuration left right
  ≤ CanonicalBlocks.canonicalGreenDegreeBlock
      (canonicalInputsAt dataSet configuration) left right
relativeGreenSound dataSet configuration inRegion left right =
  subst
    (λ lower → lower ≤
      CanonicalBlocks.canonicalGreenDegreeBlock
        (canonicalInputsAt dataSet configuration) left right)
    (sym (relativeGreenEndpointIsSchurEndpoint
      dataSet configuration inRegion left right))
    (GreenSchur.greenLowerFromSchurNormsSound
      (localSchurData dataSet configuration inRegion) left right)

relativeEnvelopeAt :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Interval.JointDegreeEnvelope
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
relativeEnvelopeAt dataSet configuration inRegion = record
  { Interval.JointDegreeEnvelope.raw1 = raw Degree.degree1
  ; Interval.JointDegreeEnvelope.raw2 = raw Degree.degree2
  ; Interval.JointDegreeEnvelope.raw3 = raw Degree.degree3
  ; Interval.JointDegreeEnvelope.raw4 = raw Degree.degree4
  ; Interval.JointDegreeEnvelope.green11 = green Degree.degree1 Degree.degree1
  ; Interval.JointDegreeEnvelope.green12 = green Degree.degree1 Degree.degree2
  ; Interval.JointDegreeEnvelope.green13 = green Degree.degree1 Degree.degree3
  ; Interval.JointDegreeEnvelope.green14 = green Degree.degree1 Degree.degree4
  ; Interval.JointDegreeEnvelope.green21 = green Degree.degree2 Degree.degree1
  ; Interval.JointDegreeEnvelope.green22 = green Degree.degree2 Degree.degree2
  ; Interval.JointDegreeEnvelope.green23 = green Degree.degree2 Degree.degree3
  ; Interval.JointDegreeEnvelope.green24 = green Degree.degree2 Degree.degree4
  ; Interval.JointDegreeEnvelope.green31 = green Degree.degree3 Degree.degree1
  ; Interval.JointDegreeEnvelope.green32 = green Degree.degree3 Degree.degree2
  ; Interval.JointDegreeEnvelope.green33 = green Degree.degree3 Degree.degree3
  ; Interval.JointDegreeEnvelope.green34 = green Degree.degree3 Degree.degree4
  ; Interval.JointDegreeEnvelope.green41 = green Degree.degree4 Degree.degree1
  ; Interval.JointDegreeEnvelope.green42 = green Degree.degree4 Degree.degree2
  ; Interval.JointDegreeEnvelope.green43 = green Degree.degree4 Degree.degree3
  ; Interval.JointDegreeEnvelope.green44 = green Degree.degree4 Degree.degree4
  }
  where
  charge = chargeAt dataSet configuration
  raw : ∀ degree →
    Interval.DegreeRawUpper
      (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
      degree
  raw degree = Interval.rawUpper
    (rawRatio dataSet degree * charge)
    (rawRelativeSound dataSet configuration inRegion degree)

  green : ∀ left right →
    Interval.DegreeGreenLower
      (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
      left right
  green left right = Interval.greenLower
    (relativeGreenEndpoint dataSet configuration left right)
    (relativeGreenSound dataSet configuration inRegion left right)

rawRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
rawRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (rawRatio dataSet)

greenRatioRow :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier →
  Degree.MobiusDegree → ℚ
greenRatioRow dataSet left =
  Sums.sumRational Degree.allDegrees (relativeGreenRatio dataSet left)

greenRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
greenRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (greenRatioRow dataSet)

residualRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
residualRatio dataSet = rawRatioTotal dataSet - greenRatioTotal dataSet

rawEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ chargeAt dataSet configuration * rawRatioTotal dataSet
rawEndpointFactorsCharge dataSet configuration inRegion =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (λ degree → ℚP.*-comm
        (rawRatio dataSet degree) (chargeAt dataSet configuration)))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees (rawRatio dataSet))

greenRowEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    left →
  Interval.greenLowerRow (relativeEnvelopeAt dataSet configuration inRegion) left
  ≡ chargeAt dataSet configuration * greenRatioRow dataSet left
greenRowEndpointFactorsCharge dataSet configuration inRegion left =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (λ right → ℚP.*-comm
        (relativeGreenRatio dataSet left right)
        (chargeAt dataSet configuration)))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees
      (relativeGreenRatio dataSet left))

greenEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.greenLowerTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ chargeAt dataSet configuration * greenRatioTotal dataSet
greenEndpointFactorsCharge dataSet configuration inRegion =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (greenRowEndpointFactorsCharge dataSet configuration inRegion))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees (greenRatioRow dataSet))

relativeEnvelopeEndpointExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (relativeEnvelopeAt dataSet configuration inRegion)
    - Interval.greenLowerTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ residualRatio dataSet * chargeAt dataSet configuration
relativeEnvelopeEndpointExact dataSet configuration inRegion
  rewrite rawEndpointFactorsCharge dataSet configuration inRegion
        | greenEndpointFactorsCharge dataSet configuration inRegion =
  ℚRing.solve-∀
    (rawRatioTotal dataSet)
    (greenRatioTotal dataSet)
    (chargeAt dataSet configuration)

relativeResidualBound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ residualRatio dataSet * chargeAt dataSet configuration
relativeResidualBound dataSet configuration inRegion =
  subst
    (λ upper →
      Ownership.correlatedResidualTotal
        (CanonicalBlocks.canonicalFamily
          (canonicalInputsAt dataSet configuration)) ≤ upper)
    (relativeEnvelopeEndpointExact dataSet configuration inRegion)
    (Interval.correlatedResidualJointDegreeUpper
      (relativeEnvelopeAt dataSet configuration inRegion))

record ChargeRelativeCanonicalG2Closure
    {Configuration Multiplier : Set}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier) : Set where
  field
    ratioFitsTarget : residualRatio dataSet ≤ Selector.remainingSingletonCoefficient
open ChargeRelativeCanonicalG2Closure public

relativeRegionG2Closes :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    (closure : ChargeRelativeCanonicalG2Closure dataSet)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
relativeRegionG2Closes dataSet closure configuration inRegion =
  let
    scaledRatio =
      Norm.scaleNonnegative
        (chargeAt dataSet configuration)
        (chargeNonnegative dataSet configuration inRegion)
        (ratioFitsTarget closure)
  in
  ℚP.≤-trans
    (relativeResidualBound dataSet configuration inRegion)
    (subst
      (λ upper →
        residualRatio dataSet * chargeAt dataSet configuration ≤ upper)
      (ℚRing.solve-∀
        Selector.remainingSingletonCoefficient
        (chargeAt dataSet configuration))
      (subst
        (λ lower → lower ≤
          chargeAt dataSet configuration * Selector.remainingSingletonCoefficient)
        (ℚRing.solve-∀
          (residualRatio dataSet)
          (chargeAt dataSet configuration))
        scaledRatio))

selectedMinimizerG2ClosesChargeRelatively :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalG2Data Configuration Multiplier)
    (closure : ChargeRelativeCanonicalG2Closure dataSet) →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerG2ClosesChargeRelatively dataSet closure =
  relativeRegionG2Closes dataSet closure
    (selectedMinimizer dataSet)
    (selectedMinimizerInRegion dataSet)

chargeRelativeCanonicalG2CompilerLevel : ProofLevel
chargeRelativeCanonicalG2CompilerLevel = machineChecked

selectedMinimizerChargeRelativeG2ClosureLevel : ProofLevel
selectedMinimizerChargeRelativeG2ClosureLevel = machineChecked

-- Remaining G2 physical theorem after this compiler:
-- prove the four raw ratios, one K+ row bound, four source-norm ratios and four
-- defect-norm ratios uniformly on the selected region, then verify the single
-- dimensionless ratio gate.  No absolute charge floor is required.
selectedRegionChargeRelativeG2NumericalTheoremLevel : ProofLevel
selectedRegionChargeRelativeG2NumericalTheoremLevel = conditional
