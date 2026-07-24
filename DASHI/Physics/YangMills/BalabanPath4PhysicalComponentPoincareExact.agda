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
axisFibreNormSum axis field =
  sumRational (physicalTransverseCoordinates side4)
    (physicalFibreNormSq field axis)

axisDirectionalEnergy : Axis4 → SiteField side4 → ℚ
axisDirectionalEnergy axis field =
  sumRational (physicalTransverseCoordinates side4)
    (physicalFibreEdgeEnergy field axis)

axisFibreNormSumIsPartition : ∀ axis field →
  axisFibreNormSum axis field
  ≡ axisPartitionSum axis (λ site → sq (field site))
axisFibreNormSumIsPartition axis field = refl

axisFibreNormSumMatchesGlobal : ∀ axis field →
  axisFibreNormSum axis field ≡ globalNormSq field
axisFibreNormSumMatchesGlobal axis field =
  trans
    (axisFibreNormSumIsPartition axis field)
    (axisPartitionSumMatchesGlobal axis (λ site → sq (field site)))

sumZeroMeanFibrePoincare :
  ∀ axis field (transverses : List (Triple (CyclicIndex side4))) →
  (∀ transverse → transverse ∈ transverses →
    physicalFibreSum field axis transverse ≡ 0ℚ) →
  sumRational transverses
    (λ transverse →
      oneSixteenth * physicalFibreNormSq field axis transverse)
  ≤ sumRational transverses
      (physicalFibreEdgeEnergy field axis)
sumZeroMeanFibrePoincare axis field [] zeroMean = ℚP.≤-refl
sumZeroMeanFibrePoincare axis field (transverse ∷ transverses) zeroMean =
  ℚP.+-mono-≤
    (zeroMeanPhysicalFibrePoincare field axis transverse
      (zeroMean transverse here))
    (sumZeroMeanFibrePoincare axis field transverses
      (λ current membership → zeroMean current (there membership)))

axisZeroMeanGlobalPoincare :
  ∀ axis field →
  (∀ transverse → physicalFibreSum field axis transverse ≡ 0ℚ) →
  oneSixteenth * globalNormSq field
  ≤ axisDirectionalEnergy axis field
axisZeroMeanGlobalPoincare axis field zeroMean =
  subst
    (λ leftValue → leftValue ≤ axisDirectionalEnergy axis field)
    (scaledGlobalNormIsFibreFold axis field)
    (sumZeroMeanFibrePoincare axis field
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

martingale0FibreMeanZero : ∀ field transverse →
  physicalFibreSum (martingaleField0 field) zeroᵢ transverse ≡ 0ℚ
martingale0FibreMeanZero field =
  axisCentering4FibreSumZero field zeroᵢ

martingale1FibreMeanZero : ∀ field transverse →
  physicalFibreSum (martingaleField1 field) (sucᵢ zeroᵢ) transverse ≡ 0ℚ
martingale1FibreMeanZero field =
  axisCentering4FibreSumZero (average0 field) (sucᵢ zeroᵢ)

martingale2FibreMeanZero : ∀ field transverse →
  physicalFibreSum (martingaleField2 field)
    (sucᵢ (sucᵢ zeroᵢ)) transverse ≡ 0ℚ
martingale2FibreMeanZero field =
  axisCentering4FibreSumZero (average01 field)
    (sucᵢ (sucᵢ zeroᵢ))

martingale3FibreMeanZero : ∀ field transverse →
  physicalFibreSum (martingaleField3 field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse ≡ 0ℚ
martingale3FibreMeanZero field =
  axisCentering4FibreSumZero (average012 field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

martingale0Poincare : ∀ field →
  oneSixteenth * globalNormSq (martingaleField0 field)
  ≤ axisDirectionalEnergy zeroᵢ (martingaleField0 field)
martingale0Poincare field =
  axisZeroMeanGlobalPoincare zeroᵢ (martingaleField0 field)
    (martingale0FibreMeanZero field)

martingale1Poincare : ∀ field →
  oneSixteenth * globalNormSq (martingaleField1 field)
  ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 field)
martingale1Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ zeroᵢ) (martingaleField1 field)
    (martingale1FibreMeanZero field)

martingale2Poincare : ∀ field →
  oneSixteenth * globalNormSq (martingaleField2 field)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) (martingaleField2 field)
martingale2Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ zeroᵢ))
    (martingaleField2 field) (martingale2FibreMeanZero field)

martingale3Poincare : ∀ field →
  oneSixteenth * globalNormSq (martingaleField3 field)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 field)
martingale3Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 field) (martingale3FibreMeanZero field)

martingaleDirectionalEnergySum : SiteField side4 → ℚ
martingaleDirectionalEnergySum field =
  axisDirectionalEnergy zeroᵢ (martingaleField0 field)
  + (axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 field)
  + (axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (martingaleField2 field)
  + axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (martingaleField3 field)))

path4MartingalePoincareBeforeEnergyContraction :
  ∀ field → GlobalMeanZero4 field →
  oneSixteenth * globalNormSq field
  ≤ martingaleDirectionalEnergySum field
path4MartingalePoincareBeforeEnergyContraction field meanZero =
  subst
    (λ leftValue → leftValue ≤ martingaleDirectionalEnergySum field)
    (scaledVarianceDecomposition field meanZero)
    (ℚP.+-mono-≤
      (martingale0Poincare field)
      (ℚP.+-mono-≤
        (martingale1Poincare field)
        (ℚP.+-mono-≤
          (martingale2Poincare field)
          (martingale3Poincare field))))
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
      (ℚRing.solve-∀
        oneSixteenth
        (globalNormSq (martingaleField0 current))
        (globalNormSq (martingaleField1 current))
        (globalNormSq (martingaleField2 current))
        (globalNormSq (martingaleField3 current)))

path4GlobalComponentPoincareLevel : ProofLevel
path4GlobalComponentPoincareLevel = machineChecked

path4MartingalePoincareSumLevel : ProofLevel
path4MartingalePoincareSumLevel = machineChecked

path4MartingaleEnergyContractionLevel : ProofLevel
path4MartingaleEnergyContractionLevel = conditional
