module DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ExactDefectCompiler where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- The degree-one G2 compiler previously still accepted two Green-state norm
-- ratios. The literal plaquette-incidence theorem now proves the defect one
-- exactly:
--
--      3 ||w_1||^2 = C_p(h).
--
-- This adapter removes the defect-ratio field from the physical interface and
-- constructs the general compiler with
--
--      defectDegreeOneNormRatio = 1/3.
--
-- Therefore the only nontrivial Green-side physical estimate left in G2 is the
-- source derivative bound. The final coefficient is
--
--   rawTotal + 1/2 (sourceRatio + 1/3).
--
-- No LBB constant, K+ row norm, or defect estimate remains as an input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact as StateNorm
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryStateNormChargeExact as Defect
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact as G2

oneThird : ℚ
oneThird = + 1 / 3

record ExactDefectDegreeOneG2Data
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

    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration →
      0ℚ ≤ Wilson.plaquetteCrossCharge
        (bondFieldAt configuration) (plaquetteAt configuration)

    rawRatio : Degree.MobiusDegree → ℚ
    sourceDegreeOneNormRatio : ℚ

    rawRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      CanonicalBlocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawRatio degree
        * Wilson.plaquetteCrossCharge
            (bondFieldAt configuration) (plaquetteAt configuration)

    sourceDegreeOneNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      StateNorm.sourceStateNormSq
        (canonicalInputsAt configuration) Degree.degree1
      ≤ sourceDegreeOneNormRatio
        * Wilson.plaquetteCrossCharge
            (bondFieldAt configuration) (plaquetteAt configuration)

open ExactDefectDegreeOneG2Data public

defectRatioExact :
  ∀ {Configuration Multiplier}
    (dataSet : ExactDefectDegreeOneG2Data Configuration Multiplier)
    configuration →
  StateNorm.defectStateNormSq
      (canonicalInputsAt dataSet configuration) Degree.degree1
  ≡ oneThird
      * Wilson.plaquetteCrossCharge
          (bondFieldAt dataSet configuration)
          (plaquetteAt dataSet configuration)
defectRatioExact dataSet configuration =
  let
    norm = StateNorm.defectStateNormSq
      (canonicalInputsAt dataSet configuration) Degree.degree1
    charge = Wilson.plaquetteCrossCharge
      (bondFieldAt dataSet configuration)
      (plaquetteAt dataSet configuration)
    triple : (+ 3 / 1) * norm ≡ charge
    triple = Defect.selectedG2DefectDegreeOneNormChargeExact
      (canonicalInputsAt dataSet configuration)
  in
  trans
    (ℚRing.solve-∀ norm)
    (cong (oneThird *_) triple)

defectRelativeSoundAutomatic :
  ∀ {Configuration Multiplier}
    (dataSet : ExactDefectDegreeOneG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  StateNorm.defectStateNormSq
      (canonicalInputsAt dataSet configuration) Degree.degree1
  ≤ oneThird
      * Wilson.plaquetteCrossCharge
          (bondFieldAt dataSet configuration)
          (plaquetteAt dataSet configuration)
defectRelativeSoundAutomatic dataSet configuration inRegion =
  subst
    (λ right →
      StateNorm.defectStateNormSq
        (canonicalInputsAt dataSet configuration) Degree.degree1 ≤ right)
    (defectRatioExact dataSet configuration)
    ℚP.≤-refl

toDegreeOneG2Data :
  ∀ {Configuration Multiplier} →
  ExactDefectDegreeOneG2Data Configuration Multiplier →
  G2.ChargeRelativeDegreeOneG2Data Configuration Multiplier
toDegreeOneG2Data dataSet = record
  { G2.ChargeRelativeDegreeOneG2Data.InCertifiedRegion =
      InCertifiedRegion dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.selectedMinimizer =
      selectedMinimizer dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.selectedMinimizerInRegion =
      selectedMinimizerInRegion dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.pseudoDataAt = pseudoDataAt dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.firstVariationAt = firstVariationAt dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.bondFieldAt = bondFieldAt dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.plaquetteAt = plaquetteAt dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.canonicalInputsAt = canonicalInputsAt dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.chargeAt = λ configuration →
      Wilson.plaquetteCrossCharge
        (bondFieldAt dataSet configuration) (plaquetteAt dataSet configuration)
  ; G2.ChargeRelativeDegreeOneG2Data.chargeNonnegative =
      chargeNonnegative dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.rawRatio = rawRatio dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.sourceDegreeOneNormRatio =
      sourceDegreeOneNormRatio dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.defectDegreeOneNormRatio = oneThird
  ; G2.ChargeRelativeDegreeOneG2Data.rawRelativeSound = rawRelativeSound dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.sourceDegreeOneNormRelativeSound =
      sourceDegreeOneNormRelativeSound dataSet
  ; G2.ChargeRelativeDegreeOneG2Data.defectDegreeOneNormRelativeSound =
      defectRelativeSoundAutomatic dataSet
  }

exactDefectResidualRatio :
  ∀ {Configuration Multiplier} →
  ExactDefectDegreeOneG2Data Configuration Multiplier → ℚ
exactDefectResidualRatio dataSet =
  G2.residualRatio (toDegreeOneG2Data dataSet)

exactDefectResidualRatioFormula :
  ∀ {Configuration Multiplier}
    (dataSet : ExactDefectDegreeOneG2Data Configuration Multiplier) →
  exactDefectResidualRatio dataSet
  ≡ G2.rawRatioTotal (toDegreeOneG2Data dataSet)
    + (+ 1 / 2) * (sourceDegreeOneNormRatio dataSet + oneThird)
exactDefectResidualRatioFormula dataSet = ℚRing.solve-∀
  (G2.rawRatioTotal (toDegreeOneG2Data dataSet))
  (sourceDegreeOneNormRatio dataSet)

chargeRelativeDegreeOneExactDefectCompilerLevel : ProofLevel
chargeRelativeDegreeOneExactDefectCompilerLevel = machineChecked
