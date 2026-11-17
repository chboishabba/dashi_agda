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
axisFibreNormSum axis fld =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreNormSq fld axis)

axisFibreNormSumMatchesGlobal : ∀ axis fld →
  axisFibreNormSum axis fld ≡ Norm.globalNormSq fld
axisFibreNormSumMatchesGlobal axis fld =
  axisPartitionSumMatchesGlobal axis (λ site → sq (fld site))

axisZeroMeanGlobalPoincare :
  ∀ axis fld →
  (∀ transverse → physicalFibreSum fld axis transverse ≡ Data.Rational.0ℚ) →
  LDL.oneEighteenth * Norm.globalNormSq fld
  ≤ Direction.axisDirectionalEnergy axis fld
axisZeroMeanGlobalPoincare axis fld zeroMean =
  let
    transverses = physicalTransverseCoordinates Side13.side13
    folded = FibreLift13.sumZeroMeanFibrePoincareViaFibre
      axis fld transverses zeroMean
    scaledGlobal :
      LDL.oneEighteenth * Norm.globalNormSq fld
      ≡ sumRational transverses
          (λ transverse →
            LDL.oneEighteenth * physicalFibreNormSq fld axis transverse)
    scaledGlobal =
      trans
        (cong (LDL.oneEighteenth *_)
          (sym (axisFibreNormSumMatchesGlobal axis fld)))
        (sym
          (sumRationalScale LDL.oneEighteenth transverses
            (physicalFibreNormSq fld axis)))
  in
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy axis fld)
    (sym scaledGlobal) folded


martingale0FibreMeanZero : ∀ fld transverse →
  physicalFibreSum
    (Martingale.martingale0 Side13.side13AverageData fld)
    zeroᵢ transverse ≡ Data.Rational.0ℚ
martingale0FibreMeanZero fld transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    fld zeroᵢ transverse

martingale1FibreMeanZero : ∀ fld transverse →
  physicalFibreSum
    (Martingale.martingale1 Side13.side13AverageData fld)
    (sucᵢ zeroᵢ) transverse ≡ Data.Rational.0ℚ
martingale1FibreMeanZero fld transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average0 Side13.side13AverageData fld)
    (sucᵢ zeroᵢ) transverse

martingale2FibreMeanZero : ∀ fld transverse →
  physicalFibreSum
    (Martingale.martingale2 Side13.side13AverageData fld)
    (sucᵢ (sucᵢ zeroᵢ)) transverse ≡ Data.Rational.0ℚ
martingale2FibreMeanZero fld transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average01 Side13.side13AverageData fld)
    (sucᵢ (sucᵢ zeroᵢ)) transverse

martingale3FibreMeanZero : ∀ fld transverse →
  physicalFibreSum
    (Martingale.martingale3 Side13.side13AverageData fld)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse ≡ Data.Rational.0ℚ
martingale3FibreMeanZero fld transverse =
  Average.axisCenteringFibreSumZero Side13.side13AverageData
    (Martingale.average012 Side13.side13AverageData fld)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse

martingale0Poincare : ∀ fld →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy zeroᵢ
      (Martingale.martingale0 Side13.side13AverageData fld)
martingale0Poincare fld =
  axisZeroMeanGlobalPoincare zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData fld)
    (martingale0FibreMeanZero fld)

martingale1Poincare : ∀ fld →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData fld)
martingale1Poincare fld =
  axisZeroMeanGlobalPoincare (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData fld)
    (martingale1FibreMeanZero fld)

martingale2Poincare : ∀ fld →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData fld)
martingale2Poincare fld =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData fld)
    (martingale2FibreMeanZero fld)

martingale3Poincare : ∀ fld →
  LDL.oneEighteenth
    * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData fld)
martingale3Poincare fld =
  axisZeroMeanGlobalPoincare (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData fld)
    (martingale3FibreMeanZero fld)

martingaleDirectionalEnergySum : SiteField Side13.side13 → ℚ
martingaleDirectionalEnergySum fld =
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData fld)
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
      (Martingale.martingale1 Side13.side13AverageData fld)
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
      (Martingale.martingale2 Side13.side13AverageData fld)
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (Martingale.martingale3 Side13.side13AverageData fld)))

martingalePoincareBeforeEnergyContraction :
  ∀ fld → Martingale.GlobalMeanZero Side13.side13AverageData fld →
  LDL.oneEighteenth * Norm.globalNormSq fld
  ≤ martingaleDirectionalEnergySum fld
martingalePoincareBeforeEnergyContraction fld meanZero =
  let
    scaledVariance :
      LDL.oneEighteenth * Norm.globalNormSq fld
      ≡ LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale0 Side13.side13AverageData fld)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale1 Side13.side13AverageData fld)
        + (LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale2 Side13.side13AverageData fld)
        + LDL.oneEighteenth
          * Norm.globalNormSq (Martingale.martingale3 Side13.side13AverageData fld)))
    scaledVariance =
      trans
        (cong (LDL.oneEighteenth *_)
          (Martingale.fourAxisVarianceDecomposition
            Side13.side13AverageData fld meanZero))
        (OpaqueAlgebra.scaleFourSum
          LDL.oneEighteenth
          (Norm.globalNormSq
            (Martingale.martingale0 Side13.side13AverageData fld))
          (Norm.globalNormSq
            (Martingale.martingale1 Side13.side13AverageData fld))
          (Norm.globalNormSq
            (Martingale.martingale2 Side13.side13AverageData fld))
          (Norm.globalNormSq
            (Martingale.martingale3 Side13.side13AverageData fld)))
  in
  subst
    (λ left → left ≤ martingaleDirectionalEnergySum fld)
    (sym scaledVariance)
    (ℚP.+-mono-≤
      (martingale0Poincare fld)
      (ℚP.+-mono-≤
        (martingale1Poincare fld)
        (ℚP.+-mono-≤
          (martingale2Poincare fld)
          (martingale3Poincare fld))))

axisCenteringEdgeDifferenceExact :
  ∀ fld axis transverse predecessor →
  Average.axisCentering Side13.side13AverageData fld axis
      (insertAxis axis (sucᵢ predecessor) transverse)
  - Average.axisCentering Side13.side13AverageData fld axis
      (insertAxis axis (weakenIndex predecessor) transverse)
  ≡ fld (insertAxis axis (sucᵢ predecessor) transverse)
    - fld (insertAxis axis (weakenIndex predecessor) transverse)
axisCenteringEdgeDifferenceExact fld axis transverse predecessor
  rewrite Average.axisAverageConstantOnFibre Side13.side13AverageData
      fld axis transverse (sucᵢ predecessor)
        | Average.axisAverageConstantOnFibre Side13.side13AverageData
      fld axis transverse (weakenIndex predecessor) =
  OpaqueAlgebra.subtractShiftCancel
    (fld (insertAxis axis (sucᵢ predecessor) transverse))
    (fld (insertAxis axis (weakenIndex predecessor) transverse))
    (Average.weight Side13.side13AverageData * physicalFibreSum fld axis transverse)



axisCenteringFibreEnergyExact : ∀ fld axis transverse →
  physicalFibreEdgeEnergy
    (Average.axisCentering Side13.side13AverageData fld axis) axis transverse
  ≡ physicalFibreEdgeEnergy fld axis transverse
axisCenteringFibreEnergyExact fld axis transverse =
  sumRationalCong
    (allCyclicIndices Direction.side12)
    _ _
    (λ predecessor →
      cong sq (axisCenteringEdgeDifferenceExact
        fld axis transverse predecessor))

axisCenteringDirectionalEnergyExact : ∀ fld axis →
  Direction.axisDirectionalEnergy axis
    (Average.axisCentering Side13.side13AverageData fld axis)
  ≡ Direction.axisDirectionalEnergy axis fld
axisCenteringDirectionalEnergyExact fld axis =
  sumRationalCong
    (physicalTransverseCoordinates Side13.side13)
    _ _
    (axisCenteringFibreEnergyExact fld axis)

axis0≢axis1 : _≢_ {A = Axis4} zeroᵢ (sucᵢ zeroᵢ)
axis0≢axis1 = zeroNotSuc

axis0≢axis2 : _≢_ {A = Axis4} zeroᵢ (sucᵢ (sucᵢ zeroᵢ))
axis0≢axis2 = zeroNotSuc

axis1≢axis2 : _≢_ {A = Axis4} (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
axis1≢axis2 eq = zeroNotSuc (sucInjective eq)

axis0≢axis3 : _≢_ {A = Axis4} zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
axis0≢axis3 = zeroNotSuc

axis1≢axis3 : _≢_ {A = Axis4} (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
axis1≢axis3 eq = zeroNotSuc (sucInjective eq)

axis2≢axis3 : _≢_ {A = Axis4} (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
axis2≢axis3 eq = zeroNotSuc (sucInjective (sucInjective eq))


martingale0DirectionalEnergyExact : ∀ fld →
  Direction.axisDirectionalEnergy zeroᵢ
    (Martingale.martingale0 Side13.side13AverageData fld)
  ≡ Direction.axisDirectionalEnergy zeroᵢ fld
martingale0DirectionalEnergyExact fld =
  axisCenteringDirectionalEnergyExact fld zeroᵢ

martingale1DirectionalEnergyBelow : ∀ fld →
  Direction.axisDirectionalEnergy (sucᵢ zeroᵢ)
    (Martingale.martingale1 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) fld
martingale1DirectionalEnergyBelow fld =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) fld)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average0 Side13.side13AverageData fld) (sucᵢ zeroᵢ)))
    (Direction.distinctAxisDirectionalEnergyContraction
      zeroᵢ (sucᵢ zeroᵢ) fld axis0≢axis1)

martingale2DirectionalEnergyBelow : ∀ fld →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ))
    (Martingale.martingale2 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fld
martingale2DirectionalEnergyBelow fld =
  subst
    (λ left → left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fld)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average01 Side13.side13AverageData fld)
      (sucᵢ (sucᵢ zeroᵢ))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
        (Martingale.average0 Side13.side13AverageData fld) axis1≢axis2)
      (Direction.distinctAxisDirectionalEnergyContraction
        zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) fld axis0≢axis2))

martingale3DirectionalEnergyBelow : ∀ fld →
  Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (Martingale.martingale3 Side13.side13AverageData fld)
  ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld
martingale3DirectionalEnergyBelow fld =
  subst
    (λ left →
      left ≤ Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld)
    (sym (axisCenteringDirectionalEnergyExact
      (Martingale.average012 Side13.side13AverageData fld)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))))
    (ℚP.≤-trans
      (Direction.distinctAxisDirectionalEnergyContraction
        (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
        (Martingale.average01 Side13.side13AverageData fld) axis2≢axis3)
      (ℚP.≤-trans
        (Direction.distinctAxisDirectionalEnergyContraction
          (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          (Martingale.average0 Side13.side13AverageData fld) axis1≢axis3)
        (Direction.distinctAxisDirectionalEnergyContraction
          zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld axis0≢axis3)))

globalDirectionalEnergy : SiteField Side13.side13 → ℚ
globalDirectionalEnergy fld =
  Direction.axisDirectionalEnergy zeroᵢ fld
  + (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) fld
  + (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fld
  + Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld))

martingaleDirectionalEnergyContraction : ∀ fld →
  martingaleDirectionalEnergySum fld ≤ globalDirectionalEnergy fld
martingaleDirectionalEnergyContraction fld =
  ℚP.+-mono-≤
    (subst
      (λ value → value ≤ Direction.axisDirectionalEnergy zeroᵢ fld)
      (sym (martingale0DirectionalEnergyExact fld)) ℚP.≤-refl)
    (ℚP.+-mono-≤
      (martingale1DirectionalEnergyBelow fld)
      (ℚP.+-mono-≤
        (martingale2DirectionalEnergyBelow fld)
        (martingale3DirectionalEnergyBelow fld)))

path13GlobalPoincare :
  ∀ fld → Martingale.GlobalMeanZero Side13.side13AverageData fld →
  LDL.oneEighteenth * Norm.globalNormSq fld
  ≤ globalDirectionalEnergy fld
path13GlobalPoincare fld meanZero =
  ℚP.≤-trans
    (martingalePoincareBeforeEnergyContraction fld meanZero)
    (martingaleDirectionalEnergyContraction fld)

path13FourAxisPhysicalPoincareLevel : ProofLevel
path13FourAxisPhysicalPoincareLevel = machineChecked
