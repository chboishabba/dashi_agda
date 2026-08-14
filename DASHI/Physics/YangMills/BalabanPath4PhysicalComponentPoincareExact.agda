module DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate using
  (oneSixteenth)
open import DASHI.Physics.YangMills.BalabanPath4ZeroMeanFibrePoincareExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact

------------------------------------------------------------------------
-- Sum the literal mean-zero P4 certificate over every transverse fibre.
------------------------------------------------------------------------

axisFibreNormSum : Axis4 → SiteField side4 → ℚ
axisFibreNormSum axis fieldValue =
  sumRational (physicalTransverseCoordinates side4)
    (physicalFibreNormSq fieldValue axis)

axisDirectionalEnergy : Axis4 → SiteField side4 → ℚ
axisDirectionalEnergy axis fieldValue =
  sumRational (physicalTransverseCoordinates side4)
    (physicalFibreEdgeEnergy fieldValue axis)

axisFibreNormSumIsPartition : ∀ axis fieldValue →
  axisFibreNormSum axis fieldValue
  ≡ axisPartitionSum axis (λ site → sq (fieldValue site))
axisFibreNormSumIsPartition axis fieldValue = refl

axisFibreNormSumMatchesGlobal : ∀ axis fieldValue →
  axisFibreNormSum axis fieldValue ≡ globalNormSq fieldValue
axisFibreNormSumMatchesGlobal axis fieldValue =
  trans
    (axisFibreNormSumIsPartition axis fieldValue)
    (axisPartitionSumMatchesGlobal axis (λ site → sq (fieldValue site)))

sumZeroMeanFibrePoincare :
  ∀ axis fieldValue (transverses : List (Triple (CyclicIndex side4))) →
  (∀ transverse → transverse ∈ transverses →
    physicalFibreSum fieldValue axis transverse ≡ 0ℚ) →
  sumRational transverses
    (λ transverse →
      oneSixteenth * physicalFibreNormSq fieldValue axis transverse)
  ≤ sumRational transverses
      (physicalFibreEdgeEnergy fieldValue axis)
sumZeroMeanFibrePoincare axis fieldValue [] zeroMean = ℚP.≤-refl
sumZeroMeanFibrePoincare axis fieldValue (transverse ∷ transverses) zeroMean =
  ℚP.+-mono-≤
    (zeroMeanPhysicalFibrePoincare fieldValue axis transverse
      (zeroMean transverse here))
    (sumZeroMeanFibrePoincare axis fieldValue transverses
      (λ current membership → zeroMean current (there membership)))

axisZeroMeanGlobalPoincare :
  ∀ axis fieldValue →
  (∀ transverse → physicalFibreSum fieldValue axis transverse ≡ 0ℚ) →
  oneSixteenth * globalNormSq fieldValue
  ≤ axisDirectionalEnergy axis fieldValue
axisZeroMeanGlobalPoincare axis fieldValue zeroMean =
  subst
    (λ leftValue → leftValue ≤ axisDirectionalEnergy axis fieldValue)
    (scaledGlobalNormIsFibreFold axis fieldValue)
    (sumZeroMeanFibrePoincare axis fieldValue
      (physicalTransverseCoordinates side4)
      (λ transverse membership → zeroMean transverse))
  where
  scaledGlobalNormIsFibreFold : ∀ currentAxis currentField →
    oneSixteenth * globalNormSq currentField
    ≡ sumRational (physicalTransverseCoordinates side4)
        (λ transverse →
          oneSixteenth
          * physicalFibreNormSq currentField currentAxis transverse)
  scaledGlobalNormIsFibreFold currentAxis currentField =
    trans
      (cong (oneSixteenth *_) (sym
        (axisFibreNormSumMatchesGlobal currentAxis currentField)))
      (sym
        (sumRationalScale
          oneSixteenth
          (physicalTransverseCoordinates side4)
          (physicalFibreNormSq currentField currentAxis)))

------------------------------------------------------------------------
-- The four martingales are zero mean in their own coordinate direction.
------------------------------------------------------------------------

martingale0FibreMeanZero : ∀ fieldValue transverse →
  physicalFibreSum (martingaleField0 fieldValue) zeroᵢ transverse ≡ 0ℚ
martingale0FibreMeanZero fieldValue =
  axisCentering4FibreSumZero fieldValue zeroᵢ

martingale1FibreMeanZero : ∀ fieldValue transverse →
  physicalFibreSum (martingaleField1 fieldValue) (sucᵢ zeroᵢ) transverse ≡ 0ℚ
martingale1FibreMeanZero fieldValue =
  axisCentering4FibreSumZero (average0 fieldValue) (sucᵢ zeroᵢ)

martingale2FibreMeanZero : ∀ fieldValue transverse →
  physicalFibreSum (martingaleField2 fieldValue)
    (sucᵢ (sucᵢ zeroᵢ)) transverse ≡ 0ℚ
martingale2FibreMeanZero fieldValue =
  axisCentering4FibreSumZero (average01 fieldValue)
    (sucᵢ (sucᵢ zeroᵢ))

martingale3FibreMeanZero : ∀ fieldValue transverse →
  physicalFibreSum (martingaleField3 fieldValue)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse ≡ 0ℚ
martingale3FibreMeanZero fieldValue =
  axisCentering4FibreSumZero (average012 fieldValue)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

martingale0Poincare : ∀ fieldValue →
  oneSixteenth * globalNormSq (martingaleField0 fieldValue)
  ≤ axisDirectionalEnergy zeroᵢ (martingaleField0 fieldValue)
martingale0Poincare fieldValue =
  axisZeroMeanGlobalPoincare zeroᵢ (martingaleField0 fieldValue)
    (martingale0FibreMeanZero fieldValue)

martingale1Poincare : ∀ fieldValue →
  oneSixteenth * globalNormSq (martingaleField1 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 fieldValue)
martingale1Poincare fieldValue =
  axisZeroMeanGlobalPoincare (sucᵢ zeroᵢ) (martingaleField1 fieldValue)
    (martingale1FibreMeanZero fieldValue)

martingale2Poincare : ∀ fieldValue →
  oneSixteenth * globalNormSq (martingaleField2 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) (martingaleField2 fieldValue)
martingale2Poincare fieldValue =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ zeroᵢ))
    (martingaleField2 fieldValue) (martingale2FibreMeanZero fieldValue)

martingale3Poincare : ∀ fieldValue →
  oneSixteenth * globalNormSq (martingaleField3 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 fieldValue)
martingale3Poincare fieldValue =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 fieldValue) (martingale3FibreMeanZero fieldValue)

martingaleDirectionalEnergySum : SiteField side4 → ℚ
martingaleDirectionalEnergySum fieldValue =
  axisDirectionalEnergy zeroᵢ (martingaleField0 fieldValue)
  + (axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 fieldValue)
  + (axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (martingaleField2 fieldValue)
  + axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (martingaleField3 fieldValue)))

path4MartingalePoincareBeforeEnergyContraction :
  ∀ fieldValue → GlobalMeanZero4 fieldValue →
  oneSixteenth * globalNormSq fieldValue
  ≤ martingaleDirectionalEnergySum fieldValue
path4MartingalePoincareBeforeEnergyContraction fieldValue meanZero =
  subst
    (λ leftValue → leftValue ≤ martingaleDirectionalEnergySum fieldValue)
    (scaledVarianceDecomposition fieldValue meanZero)
    (ℚP.+-mono-≤
      (martingale0Poincare fieldValue)
      (ℚP.+-mono-≤
        (martingale1Poincare fieldValue)
        (ℚP.+-mono-≤
          (martingale2Poincare fieldValue)
          (martingale3Poincare fieldValue))))
  where
  scaledVarianceDecomposition : ∀ current → GlobalMeanZero4 current →
    oneSixteenth * globalNormSq current
    ≡ oneSixteenth * globalNormSq (martingaleField0 current)
      + (oneSixteenth * globalNormSq (martingaleField1 current)
      + (oneSixteenth * globalNormSq (martingaleField2 current)
      + oneSixteenth * globalNormSq (martingaleField3 current)))
  scaledVarianceDecomposition current currentMeanZero =
    trans
      (cong (oneSixteenth *_)
        (physicalMartingaleVarianceDecomposition current currentMeanZero))
      (ℚRing.solve-∀)

path4GlobalComponentPoincareLevel : ProofLevel
path4GlobalComponentPoincareLevel = machineChecked

path4MartingalePoincareSumLevel : ProofLevel
path4MartingalePoincareSumLevel = machineChecked

path4MartingaleEnergyContractionLevel : ProofLevel
path4MartingaleEnergyContractionLevel = conditional
