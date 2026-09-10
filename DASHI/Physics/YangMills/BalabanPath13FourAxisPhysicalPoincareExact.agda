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
-- directional edge energies.  Hence, for every literal side-13 block siteField
-- whose terminal four-axis average vanishes,
--
--       (1/18) ||h||_2^2 <= sum_{axis,fibre} E_axis(h).
--
-- This is the requested same-carrier replacement for the side-four scalar
-- coercivity input and is the direct precursor to the SU(2)-component lift.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
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
import DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact as OpaqueAlgebra
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13ZeroMeanFibrePoincareLiftExact as FibreLift13
import DASHI.Physics.YangMills.BalabanPath13DirectionalEnergyContractionExact as Direction

axisFibreNormSum : Axis4 → SiteField Side13.side13 → ℚ
axisFibreNormSum axis siteField =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreNormSq siteField axis)

axisFibreNormSumMatchesGlobal : ∀ axis siteField →
  axisFibreNormSum axis siteField ≡ Norm.globalNormSq siteField
axisFibreNormSumMatchesGlobal axis siteField =
  axisPartitionSumMatchesGlobal axis (λ site → sq (siteField site))

axisZeroMeanGlobalPoincare :
  ∀ axis siteField →
  (∀ transverse → physicalFibreSum siteField axis transverse ≡ Data.Rational.0ℚ) →
  LDL.oneEighteenth * Norm.globalNormSq siteField
  ≤ Direction.axisDirectionalEnergy axis siteField
axisZeroMeanGlobalPoincare axis siteField zeroMean =
  let
    transverses = physicalTransverseCoordinates Side13.side13
    folded = FibreLift13.sumZeroMeanFibrePoincareViaFibre
      axis siteField transverses zeroMean
    scaledGlobal :
      LDL.oneEighteenth * Norm.globalNormSq siteField
      ≡ sumRational transverses
          (λ transverse →
            LDL.oneEighteenth * physicalFibreNormSq siteField axis transverse)
    scaledGlobal =
      trans
        (cong (LDL.oneEighteenth *_)
          (sym (axisFibreNormSumMatchesGlobal axis siteField)))
        (sym
          (sumRationalScale LDL.oneEighteenth transverses
            (physicalFibreNormSq siteField axis)))
  in
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy axis siteField)
    scaledGlobal folded

martingale0FibreMeanZero : ∀ siteField transverse →
  physicalFibreSum
    (Martingale.martingale0 Side13.side13AverageData siteField)
    zeroᵢ transverse ≡ Data.Rational.0ℚ
martingale0FibreMeanZero siteField transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    siteField zeroᵢ transverse

martingale1FibreMeanZero : ∀ siteField transverse →
  physicalFibreSum
    (Martingale.martingale1 Side13.side13AverageData siteField)
    (sucᵢ zeroᵢ) transverse ≡ Data.Rational.0ℚ
martingale1FibreMeanZero siteField transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average0 Side13.side13AverageData siteField)
    (sucᵢ zeroᵢ) transverse

martingale2FibreMeanZero : ∀ siteField transverse →
  physicalFibreSum
    (Martingale.martingale2 Side13.side13AverageData siteField)
    (sucᵢ (sucᵢ zeroᵢ)) transverse ≡ Data.Rational.0ℚ
martingale2FibreMeanZero siteField transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average01 Side13.side13AverageData siteField)
    (sucᵢ (sucᵢ zeroᵢ)) transverse

martingale3FibreMeanZero : ∀ siteField transverse →
  physicalFibreSum
    (Martingale.martingale3 Side13.side13AverageData siteField)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse ≡ Data.Rational.0ℚ
martingale3FibreMeanZero siteField transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average012 Side13.side13AverageData siteField)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse

martingale0Poincare : ∀ siteField →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy zeroᵢ
      (Martingale.martingale0 Side13.side13AverageData siteField)
martingale0Poincare siteField =
  axisZeroMeanGlobalPoincare zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData siteField)
    (martingale0FibreMeanZero siteField)

martingale1Poincare : ∀ siteField →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData siteField)
martingale1Poincare siteField =
  axisZeroMeanGlobalPoincare (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData siteField)
    (martingale1FibreMeanZero siteField)

martingale2Poincare : ∀ siteField →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData siteField)
martingale2Poincare siteField =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData siteField)
    (martingale2FibreMeanZero siteField)

martingale3Poincare : ∀ siteField →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData siteField)
martingale3Poincare siteField =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData siteField)
    (martingale3FibreMeanZero siteField)

martingaleDirectionalEnergySum : SiteField Side13.side13 → ℚ
martingaleDirectionalEnergySum siteField =
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData siteField)
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData siteField)
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData siteField)
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData siteField)))

martingalePoincareBeforeEnergyContraction :
  ∀ siteField → Martingale.GlobalMeanZero Side13.side13AverageData siteField →
  LDL.oneEighteenth * Norm.globalNormSq siteField
  ≤ martingaleDirectionalEnergySum siteField
martingalePoincareBeforeEnergyContraction siteField meanZero =
  let
    scaledVariance :
      LDL.oneEighteenth * Norm.globalNormSq siteField
      ≡ LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData siteField)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData siteField)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData siteField)
        + LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData siteField)))
    scaledVariance =
      trans
        (cong (LDL.oneEighteenth *_)
          (Martingale.fourAxisVarianceDecomposition
            Side13.side13AverageData siteField meanZero))
        (OpaqueAlgebra.scaleFourSum
          LDL.oneEighteenth
          (Norm.globalNormSq
            (Martingale.martingale0 Side13.side13AverageData siteField))
          (Norm.globalNormSq
            (Martingale.martingale1 Side13.side13AverageData siteField))
          (Norm.globalNormSq
            (Martingale.martingale2 Side13.side13AverageData siteField))
          (Norm.globalNormSq
            (Martingale.martingale3 Side13.side13AverageData siteField)))
  in
  subst
    (λ left → left ≤ martingaleDirectionalEnergySum siteField)
    scaledVariance
    (ℚP.+-mono-≤
      (martingale0Poincare siteField)
      (ℚP.+-mono-≤
        (martingale1Poincare siteField)
        (ℚP.+-mono-≤
          (martingale2Poincare siteField)
          (martingale3Poincare siteField))))

axisCenteringEdgeDifferenceExact :
  ∀ siteField axis transverse predecessor →
  Average.axisCentering Side13.side13AverageData siteField axis
      (insertAxis axis (sucᵢ predecessor) transverse)
  - Average.axisCentering Side13.side13AverageData siteField axis
      (insertAxis axis (weakenIndex predecessor) transverse)
  ≡ siteField (insertAxis axis (sucᵢ predecessor) transverse)
    - siteField (insertAxis axis (weakenIndex predecessor) transverse)
axisCenteringEdgeDifferenceExact siteField axis transverse predecessor
  rewrite Average.axisAverageConstantOnFibre Side13.side13AverageData
      siteField axis transverse (sucᵢ predecessor)
        | Average.axisAverageConstantOnFibre Side13.side13AverageData
      siteField axis transverse (weakenIndex predecessor) =
  OpaqueAlgebra.subtractShiftCancel _ _ _

axisCenteringFibreEnergyExact : ∀ siteField axis transverse →
  physicalFibreEdgeEnergy
    (Average.axisCentering Side13.side13AverageData siteField axis) axis transverse
  ≡ physicalFibreEdgeEnergy siteField axis transverse
axisCenteringFibreEnergyExact siteField axis transverse =
  sumRationalCong
    (allCyclicIndices Direction.side12)
    _ _
    (λ predecessor →
      cong sq (axisCenteringEdgeDifferenceExact
        siteField axis transverse predecessor))

axisCenteringDirectionalEnergyExact : ∀ siteField axis →
  Direction.axisDirectionalEnergy axis
    (Average.axisCentering Side13.side13AverageData siteField axis)
  ≡ Direction.axisDirectionalEnergy axis siteField
axisCenteringDirectionalEnergyExact siteField axis =
  sumRationalCong
    (physicalTransverseCoordinates Side13.side13)
    _ _
    (axisCenteringFibreEnergyExact siteField axis)

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

martingale0DirectionalEnergyExact : ∀ siteField →
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData siteField)
  ≡ Direction.axisDirectionalEnergy zeroᵢ siteField
martingale0DirectionalEnergyExact siteField =
  axisCenteringDirectionalEnergyExact siteField zeroᵢ

martingale1DirectionalEnergyBelow : ∀ siteField →
  Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) siteField
martingale1DirectionalEnergyBelow siteField =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) siteField)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average0 Side13.side13AverageData siteField) (sucᵢ zeroᵢ)))
    (Direction.distinctAxisDirectionalEnergyContraction
      zeroᵢ (sucᵢ zeroᵢ) siteField axis0≢axis1)

martingale2DirectionalEnergyBelow : ∀ siteField →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) siteField
martingale2DirectionalEnergyBelow siteField =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) siteField)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average01 Side13.side13AverageData siteField)
      (sucᵢ (sucᵢ zeroᵢ))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
        (Martingale.average0 Side13.side13AverageData siteField) axis1≢axis2)
      (Direction.distinctAxisDirectionalEnergyContraction
        zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) siteField axis0≢axis2))

martingale3DirectionalEnergyBelow : ∀ siteField →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData siteField)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField
martingale3DirectionalEnergyBelow siteField =
  subst
    (λ left →
      left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average012 Side13.side13AverageData siteField)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
        (Martingale.average01 Side13.side13AverageData siteField) axis2≢axis3)
      (ℚP.≤-trans
        (Direction.distinctAxisDirectionalEnergyContraction
          (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          (Martingale.average0 Side13.side13AverageData siteField) axis1≢axis3)
        (Direction.distinctAxisDirectionalEnergyContraction
          zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField axis0≢axis3)))

globalDirectionalEnergy : SiteField Side13.side13 → ℚ
globalDirectionalEnergy siteField =
  Direction.axisDirectionalEnergy zeroᵢ siteField
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) siteField
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) siteField
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField))

martingaleDirectionalEnergyContraction : ∀ siteField →
  martingaleDirectionalEnergySum siteField ≤ globalDirectionalEnergy siteField
martingaleDirectionalEnergyContraction siteField =
  ℚP.+-mono-≤
    (subst
      (λ value → value ≤ Direction.axisDirectionalEnergy zeroᵢ siteField)
      (sym (martingale0DirectionalEnergyExact siteField)) ℚP.≤-refl)
    (ℚP.+-mono-≤
      (martingale1DirectionalEnergyBelow siteField)
      (ℚP.+-mono-≤
        (martingale2DirectionalEnergyBelow siteField)
        (martingale3DirectionalEnergyBelow siteField)))

path13GlobalPoincare :
  ∀ siteField → Martingale.GlobalMeanZero Side13.side13AverageData siteField →
  LDL.oneEighteenth * Norm.globalNormSq siteField
  ≤ globalDirectionalEnergy siteField
path13GlobalPoincare siteField meanZero =
  ℚP.≤-trans
    (martingalePoincareBeforeEnergyContraction siteField meanZero)
    (martingaleDirectionalEnergyContraction siteField)

path13FourAxisPhysicalPoincareLevel : ProofLevel
path13FourAxisPhysicalPoincareLevel = machineChecked
