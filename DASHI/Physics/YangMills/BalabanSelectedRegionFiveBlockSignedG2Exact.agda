module DASHI.Physics.YangMills.BalabanSelectedRegionFiveBlockSignedG2Exact where

------------------------------------------------------------------------
-- ROUND65: FIVE-BLOCK SIGNED G2 COMPILER
--
-- PRIMARY SOURCES
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories", CMP 102 (1985),
-- 277--309. DOI: 10.1007/BF01229381.
-- Roger Penrose, "A Generalized Inverse for Matrices", Proc. Cambridge
-- Philosophical Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Möbius Functions" (1964). DOI: 10.1007/BF00531932.
--
-- The canonical subset calculation has already proved
--
--   R_corr = R1 + R2 + R3 + R4 - G11.
--
-- Hence the sharp finite interface is four charge-relative upper bounds and
-- one charge-relative LOWER bound on G11, followed by
--
--   r1+r2+r3+r4-g <= 55/18874368.
--
-- No positive charge floor and no polarization are used.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanCanonicalCorrelatedDegreeOneBeforePolarizationExact as Signed
import DASHI.Physics.YangMills.BalabanSelectedRegionSignedG2MasterExact as Master

record FiveBlockChargeRelativeG2Data
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer
    pseudoDataAt : Configuration → Pseudo.FiniteKKTPseudoinverseData Multiplier
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
    raw1Ratio raw2Ratio raw3Ratio raw4Ratio green11LowerRatio : ℚ
    raw1RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      Blocks.canonicalRawDegreeBlock (canonicalInputsAt configuration) Degree.degree1
      ≤ raw1Ratio * chargeAt configuration
    raw2RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      Blocks.canonicalRawDegreeBlock (canonicalInputsAt configuration) Degree.degree2
      ≤ raw2Ratio * chargeAt configuration
    raw3RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      Blocks.canonicalRawDegreeBlock (canonicalInputsAt configuration) Degree.degree3
      ≤ raw3Ratio * chargeAt configuration
    raw4RelativeSound : ∀ configuration → InCertifiedRegion configuration →
      Blocks.canonicalRawDegreeBlock (canonicalInputsAt configuration) Degree.degree4
      ≤ raw4Ratio * chargeAt configuration
    green11RelativeLowerSound : ∀ configuration → InCertifiedRegion configuration →
      green11LowerRatio * chargeAt configuration
      ≤ Blocks.canonicalGreenDegreeBlock
          (canonicalInputsAt configuration) Degree.degree1 Degree.degree1
    fiveBlockCoefficientFits :
      raw1Ratio + raw2Ratio + raw3Ratio + raw4Ratio - green11LowerRatio
      ≤ Selector.remainingSingletonCoefficient

open FiveBlockChargeRelativeG2Data public

fiveBlockRatio : ∀ {Configuration Multiplier} →
  FiveBlockChargeRelativeG2Data Configuration Multiplier → ℚ
fiveBlockRatio dataSet =
  raw1Ratio dataSet + raw2Ratio dataSet + raw3Ratio dataSet + raw4Ratio dataSet
  - green11LowerRatio dataSet

fiveBlockRatioFits : ∀ {Configuration Multiplier}
  (dataSet : FiveBlockChargeRelativeG2Data Configuration Multiplier) →
  fiveBlockRatio dataSet ≤ Selector.remainingSingletonCoefficient
fiveBlockRatioFits = fiveBlockCoefficientFits

fiveBlockSignedResidualRelativeBound :
  ∀ {Configuration Multiplier}
    (dataSet : FiveBlockChargeRelativeG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ fiveBlockRatio dataSet * chargeAt dataSet configuration
fiveBlockSignedResidualRelativeBound dataSet configuration inRegion =
  let
    inputs = canonicalInputsAt dataSet configuration
    q = chargeAt dataSet configuration
    r1 = raw1RelativeSound dataSet configuration inRegion
    r2 = raw2RelativeSound dataSet configuration inRegion
    r3 = raw3RelativeSound dataSet configuration inRegion
    r4 = raw4RelativeSound dataSet configuration inRegion
    g = green11RelativeLowerSound dataSet configuration inRegion
    raw12 = ℚP.+-mono-≤ r1 r2
    raw123 = ℚP.+-mono-≤ raw12 r3
    raw1234 = ℚP.+-mono-≤ raw123 r4
    signed = ℚP.+-mono-≤ raw1234 (ℚP.neg-mono-≤ g)
    actualExpanded :
      Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs)
      ≡ Blocks.canonicalRawDegreeBlock inputs Degree.degree1
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree2
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree3
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree4
        + (- Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1)
    actualExpanded =
      let base = Signed.canonicalCorrelatedResidualDegreeOneBeforePolarization inputs
      in subst
        (λ rhs → Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs) ≡ rhs)
        (ℚRing.solve-∀
          (Blocks.canonicalRawDegreeBlock inputs Degree.degree1)
          (Blocks.canonicalRawDegreeBlock inputs Degree.degree2)
          (Blocks.canonicalRawDegreeBlock inputs Degree.degree3)
          (Blocks.canonicalRawDegreeBlock inputs Degree.degree4)
          (Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1))
        base
    coefficientExpanded :
      raw1Ratio dataSet * q + raw2Ratio dataSet * q
      + raw3Ratio dataSet * q + raw4Ratio dataSet * q
      + (- (green11LowerRatio dataSet * q))
      ≡ fiveBlockRatio dataSet * q
    coefficientExpanded = ℚRing.solve-∀
      (raw1Ratio dataSet) (raw2Ratio dataSet)
      (raw3Ratio dataSet) (raw4Ratio dataSet)
      (green11LowerRatio dataSet) q
  in
  subst (λ lower → lower ≤ fiveBlockRatio dataSet * q) (sym actualExpanded)
    (subst
      (λ upper →
        Blocks.canonicalRawDegreeBlock inputs Degree.degree1
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree2
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree3
        + Blocks.canonicalRawDegreeBlock inputs Degree.degree4
        + (- Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1)
        ≤ upper)
      coefficientExpanded signed)

fiveBlockScaledCoefficientFits :
  ∀ {Configuration Multiplier}
    (dataSet : FiveBlockChargeRelativeG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  fiveBlockRatio dataSet * chargeAt dataSet configuration
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
fiveBlockScaledCoefficientFits dataSet configuration inRegion =
  let
    q = chargeAt dataSet configuration
    scaled = Norm.scaleNonnegative q
      (chargeNonnegative dataSet configuration inRegion)
      (fiveBlockRatioFits dataSet)
  in
  subst
    (λ lower → lower ≤ Selector.remainingSingletonCoefficient * q)
    (ℚRing.solve-∀ q (fiveBlockRatio dataSet))
    (subst
      (λ upper → q * fiveBlockRatio dataSet ≤ upper)
      (ℚRing.solve-∀ q Selector.remainingSingletonCoefficient)
      scaled)

fiveBlockRegionCloses :
  ∀ {Configuration Multiplier}
    (dataSet : FiveBlockChargeRelativeG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
fiveBlockRegionCloses dataSet configuration inRegion =
  ℚP.≤-trans
    (fiveBlockSignedResidualRelativeBound dataSet configuration inRegion)
    (fiveBlockScaledCoefficientFits dataSet configuration inRegion)

fiveBlockDataToSignedMaster : ∀ {Configuration Multiplier} →
  FiveBlockChargeRelativeG2Data Configuration Multiplier →
  Master.SignedSelectedRegionG2Master Configuration Multiplier
fiveBlockDataToSignedMaster dataSet = record
  { Master.SignedSelectedRegionG2Master.InCertifiedRegion = InCertifiedRegion dataSet
  ; Master.SignedSelectedRegionG2Master.selectedMinimizer = selectedMinimizer dataSet
  ; Master.SignedSelectedRegionG2Master.selectedMinimizerInRegion = selectedMinimizerInRegion dataSet
  ; Master.SignedSelectedRegionG2Master.pseudoDataAt = pseudoDataAt dataSet
  ; Master.SignedSelectedRegionG2Master.firstVariationAt = firstVariationAt dataSet
  ; Master.SignedSelectedRegionG2Master.bondFieldAt = bondFieldAt dataSet
  ; Master.SignedSelectedRegionG2Master.plaquetteAt = plaquetteAt dataSet
  ; Master.SignedSelectedRegionG2Master.canonicalInputsAt = canonicalInputsAt dataSet
  ; Master.SignedSelectedRegionG2Master.chargeAt = chargeAt dataSet
  ; Master.SignedSelectedRegionG2Master.signedResidualAbsorbed = fiveBlockRegionCloses dataSet
  }

selectedMinimizerFiveBlockG2 : ∀ {Configuration Multiplier}
  (dataSet : FiveBlockChargeRelativeG2Data Configuration Multiplier) →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerFiveBlockG2 dataSet =
  Master.selectedMinimizerSignedG2Absorbed (fiveBlockDataToSignedMaster dataSet)

fiveBlockSignedG2CompilerLevel : ProofLevel
fiveBlockSignedG2CompilerLevel = machineChecked

physicalFiveBlockSignedG2Level : ProofLevel
physicalFiveBlockSignedG2Level = conditional
