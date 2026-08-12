module DASHI.Physics.YangMills.BalabanPath13FourAxisPhysicalPoincareExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01240221.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Close the scalar source-admissible L=13 four-dimensional Poincare theorem.
-- The exact Path13 LDL floor is applied to each zero-mean martingale fibre;
-- the arbitrary-side conditional-expectation Pythagoras theorem reconstructs
-- the full global norm; and distinct-axis averaging contracts the corresponding
-- directional edge energies.  Hence, for every literal side-13 block field
-- whose terminal four-axis average vanishes,
--
--       (1/18) ||h||_2^2 <= sum_{axis,fibre} E_axis(h).
--
-- This is the requested same-carrier replacement for the side-four scalar
-- coercivity input and is the direct precursor to the SU(2)-component lift.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact as Average
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact as Norm
import DASHI.Physics.YangMills.BalabanNormalizedFourAxisMartingaleExact as Martingale
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13ZeroMeanFibrePoincareExact as Fibre13
import DASHI.Physics.YangMills.BalabanPath13DirectionalEnergyContractionExact as Direction

axisFibreNormSum : Axis4 → SiteField Side13.side13 → ℚ
axisFibreNormSum axis field =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreNormSq field axis)

axisFibreNormSumMatchesGlobal : ∀ axis field →
  axisFibreNormSum axis field ≡ Norm.globalNormSq field
axisFibreNormSumMatchesGlobal axis field =
  axisPartitionSumMatchesGlobal axis (λ site → sq (field site))

sumZeroMeanFibrePoincare :
  ∀ axis field (transverses : List (Triple (CyclicIndex Side13.side13))) →
  (∀ transverse → transverse ∈ transverses →
    physicalFibreSum field axis transverse ≡ Data.Rational.0ℚ) →
  sumRational transverses
    (λ transverse →
      LDL.oneEighteenth * physicalFibreNormSq field axis transverse)
  ≤ sumRational transverses (physicalFibreEdgeEnergy field axis)
sumZeroMeanFibrePoincare axis field [] zeroMean = ℚP.≤-refl
sumZeroMeanFibrePoincare axis field (transverse ∷ transverses) zeroMean =
  ℚP.+-mono-≤
    (Fibre13.zeroMeanPhysicalFibrePoincare13 field axis transverse
      (zeroMean transverse here))
    (sumZeroMeanFibrePoincare axis field transverses
      (λ current membership → zeroMean current (there membership)))

axisZeroMeanGlobalPoincare :
  ∀ axis field →
  (∀ transverse → physicalFibreSum field axis transverse ≡ Data.Rational.0ℚ) →
  LDL.oneEighteenth * Norm.globalNormSq field
  ≤ Direction.axisDirectionalEnergy axis field
axisZeroMeanGlobalPoincare axis field zeroMean =
  let
    transverses = physicalTransverseCoordinates Side13.side13
    folded = sumZeroMeanFibrePoincare axis field transverses
      (λ transverse membership → zeroMean transverse)
    scaledGlobal :
      LDL.oneEighteenth * Norm.globalNormSq field
      ≡ sumRational transverses
          (λ transverse →
            LDL.oneEighteenth * physicalFibreNormSq field axis transverse)
    scaledGlobal =
      trans
        (cong (LDL.oneEighteenth *_)
          (sym (axisFibreNormSumMatchesGlobal axis field)))
        (sym
          (sumRationalScale LDL.oneEighteenth transverses
            (physicalFibreNormSq field axis)))
  in
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy axis field)
    scaledGlobal folded

martingale0FibreMeanZero : ∀ field transverse →
  physicalFibreSum
    (Martingale.martingale0 Side13.side13AverageData field)
    zeroᵢ transverse ≡ Data.Rational.0ℚ
martingale0FibreMeanZero field transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    field zeroᵢ transverse

martingale1FibreMeanZero : ∀ field transverse →
  physicalFibreSum
    (Martingale.martingale1 Side13.side13AverageData field)
    (sucᵢ zeroᵢ) transverse ≡ Data.Rational.0ℚ
martingale1FibreMeanZero field transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average0 Side13.side13AverageData field)
    (sucᵢ zeroᵢ) transverse

martingale2FibreMeanZero : ∀ field transverse →
  physicalFibreSum
    (Martingale.martingale2 Side13.side13AverageData field)
    (sucᵢ (sucᵢ zeroᵢ)) transverse ≡ Data.Rational.0ℚ
martingale2FibreMeanZero field transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average01 Side13.side13AverageData field)
    (sucᵢ (sucᵢ zeroᵢ)) transverse

martingale3FibreMeanZero : ∀ field transverse →
  physicalFibreSum
    (Martingale.martingale3 Side13.side13AverageData field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse ≡ Data.Rational.0ℚ
martingale3FibreMeanZero field transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average012 Side13.side13AverageData field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse

martingale0Poincare : ∀ field →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy zeroᵢ
      (Martingale.martingale0 Side13.side13AverageData field)
martingale0Poincare field =
  axisZeroMeanGlobalPoincare zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData field)
    (martingale0FibreMeanZero field)

martingale1Poincare : ∀ field →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData field)
martingale1Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData field)
    (martingale1FibreMeanZero field)

martingale2Poincare : ∀ field →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData field)
martingale2Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData field)
    (martingale2FibreMeanZero field)

martingale3Poincare : ∀ field →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData field)
martingale3Poincare field =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData field)
    (martingale3FibreMeanZero field)

martingaleDirectionalEnergySum : SiteField Side13.side13 → ℚ
martingaleDirectionalEnergySum field =
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData field)
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData field)
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData field)
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData field)))

martingalePoincareBeforeEnergyContraction :
  ∀ field → Martingale.GlobalMeanZero Side13.side13AverageData field →
  LDL.oneEighteenth * Norm.globalNormSq field
  ≤ martingaleDirectionalEnergySum field
martingalePoincareBeforeEnergyContraction field meanZero =
  let
    scaledVariance :
      LDL.oneEighteenth * Norm.globalNormSq field
      ≡ LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData field)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData field)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData field)
        + LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData field)))
    scaledVariance =
      trans
        (cong (LDL.oneEighteenth *_)
          (Martingale.fourAxisVarianceDecomposition
            Side13.side13AverageData field meanZero))
        (ℚRing.solve-∀)
  in
  subst
    (λ left → left ≤ martingaleDirectionalEnergySum field)
    scaledVariance
    (ℚP.+-mono-≤
      (martingale0Poincare field)
      (ℚP.+-mono-≤
        (martingale1Poincare field)
        (ℚP.+-mono-≤
          (martingale2Poincare field)
          (martingale3Poincare field))))

axisCenteringEdgeDifferenceExact :
  ∀ field axis transverse predecessor →
  Average.axisCentering Side13.side13AverageData field axis
      (insertAxis axis (sucᵢ predecessor) transverse)
  - Average.axisCentering Side13.side13AverageData field axis
      (insertAxis axis (weakenIndex predecessor) transverse)
  ≡ field (insertAxis axis (sucᵢ predecessor) transverse)
    - field (insertAxis axis (weakenIndex predecessor) transverse)
axisCenteringEdgeDifferenceExact field axis transverse predecessor
  rewrite Average.axisAverageConstantOnFibre Side13.side13AverageData
      field axis transverse (sucᵢ predecessor)
        | Average.axisAverageConstantOnFibre Side13.side13AverageData
      field axis transverse (weakenIndex predecessor) =
  ℚRing.solve-∀

axisCenteringFibreEnergyExact : ∀ field axis transverse →
  physicalFibreEdgeEnergy
    (Average.axisCentering Side13.side13AverageData field axis) axis transverse
  ≡ physicalFibreEdgeEnergy field axis transverse
axisCenteringFibreEnergyExact field axis transverse =
  sumRationalCong
    (allCyclicIndices Direction.side12)
    _ _
    (λ predecessor →
      cong sq (axisCenteringEdgeDifferenceExact
        field axis transverse predecessor))

axisCenteringDirectionalEnergyExact : ∀ field axis →
  Direction.axisDirectionalEnergy axis
    (Average.axisCentering Side13.side13AverageData field axis)
  ≡ Direction.axisDirectionalEnergy axis field
axisCenteringDirectionalEnergyExact field axis =
  sumRationalCong
    (physicalTransverseCoordinates Side13.side13)
    _ _
    (axisCenteringFibreEnergyExact field axis)

axis0≢axis1 : zeroᵢ ≢ sucᵢ zeroᵢ
axis0≢axis1 ()
axis0≢axis2 : zeroᵢ ≢ sucᵢ (sucᵢ zeroᵢ)
axis0≢axis2 ()
axis1≢axis2 : sucᵢ zeroᵢ ≢ sucᵢ (sucᵢ zeroᵢ)
axis1≢axis2 ()
axis0≢axis3 : zeroᵢ ≢ sucᵢ (sucᵢ (sucᵢ zeroᵢ))
axis0≢axis3 ()
axis1≢axis3 : sucᵢ zeroᵢ ≢ sucᵢ (sucᵢ (sucᵢ zeroᵢ))
axis1≢axis3 ()
axis2≢axis3 : sucᵢ (sucᵢ zeroᵢ) ≢ sucᵢ (sucᵢ (sucᵢ zeroᵢ))
axis2≢axis3 ()

martingale0DirectionalEnergyExact : ∀ field →
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData field)
  ≡ Direction.axisDirectionalEnergy zeroᵢ field
martingale0DirectionalEnergyExact field =
  axisCenteringDirectionalEnergyExact field zeroᵢ

martingale1DirectionalEnergyBelow : ∀ field →
  Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) field
martingale1DirectionalEnergyBelow field =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) field)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average0 Side13.side13AverageData field) (sucᵢ zeroᵢ)))
    (Direction.distinctAxisDirectionalEnergyContraction
      zeroᵢ (sucᵢ zeroᵢ) field axis0≢axis1)

martingale2DirectionalEnergyBelow : ∀ field →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field
martingale2DirectionalEnergyBelow field =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average01 Side13.side13AverageData field)
      (sucᵢ (sucᵢ zeroᵢ))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
        (Martingale.average0 Side13.side13AverageData field) axis1≢axis2)
      (Direction.distinctAxisDirectionalEnergyContraction
        zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) field axis0≢axis2))

martingale3DirectionalEnergyBelow : ∀ field →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData field)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field
martingale3DirectionalEnergyBelow field =
  subst
    (λ left →
      left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average012 Side13.side13AverageData field)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
        (Martingale.average01 Side13.side13AverageData field) axis2≢axis3)
      (ℚP.≤-trans
        (Direction.distinctAxisDirectionalEnergyContraction
          (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          (Martingale.average0 Side13.side13AverageData field) axis1≢axis3)
        (Direction.distinctAxisDirectionalEnergyContraction
          zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field axis0≢axis3)))

globalDirectionalEnergy : SiteField Side13.side13 → ℚ
globalDirectionalEnergy field =
  Direction.axisDirectionalEnergy zeroᵢ field
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) field
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field))

martingaleDirectionalEnergyContraction : ∀ field →
  martingaleDirectionalEnergySum field ≤ globalDirectionalEnergy field
martingaleDirectionalEnergyContraction field =
  ℚP.+-mono-≤
    (subst
      (λ value → value ≤ Direction.axisDirectionalEnergy zeroᵢ field)
      (sym (martingale0DirectionalEnergyExact field)) ℚP.≤-refl)
    (ℚP.+-mono-≤
      (martingale1DirectionalEnergyBelow field)
      (ℚP.+-mono-≤
        (martingale2DirectionalEnergyBelow field)
        (martingale3DirectionalEnergyBelow field)))

path13GlobalPoincare :
  ∀ field → Martingale.GlobalMeanZero Side13.side13AverageData field →
  LDL.oneEighteenth * Norm.globalNormSq field
  ≤ globalDirectionalEnergy field
path13GlobalPoincare field meanZero =
  ℚP.≤-trans
    (martingalePoincareBeforeEnergyContraction field meanZero)
    (martingaleDirectionalEnergyContraction field)

path13FourAxisPhysicalPoincareLevel : ProofLevel
path13FourAxisPhysicalPoincareLevel = machineChecked
