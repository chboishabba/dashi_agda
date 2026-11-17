module DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate using
  (oneSixteenth)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact

------------------------------------------------------------------------
-- Close the scalar side-four tensorization theorem.
--
-- Each martingale is a centering in its own coordinate.  Centering leaves
-- differences in that coordinate unchanged, while every earlier distinct-axis
-- average contracts that directional energy.  Summing the four component
-- bounds closes the global side-four Poincare estimate.
------------------------------------------------------------------------

axisCenteringEdgeDifferenceExact :
  ∀ fieldValue axis transverse predecessor →
  axisCentering4 fieldValue axis
      (insertAxis axis (sucᵢ predecessor) transverse)
  - axisCentering4 fieldValue axis
      (insertAxis axis (weakenIndex predecessor) transverse)
  ≡ fieldValue (insertAxis axis (sucᵢ predecessor) transverse)
    - fieldValue (insertAxis axis (weakenIndex predecessor) transverse)
axisCenteringEdgeDifferenceExact fieldValue axis transverse predecessor
  rewrite axisCentering4OnFibre fieldValue axis transverse (sucᵢ predecessor)
        | axisCentering4OnFibre fieldValue axis transverse (weakenIndex predecessor) =
  ℚRing.solve-∀

axisCenteringFibreEnergyExact : ∀ fieldValue axis transverse →
  physicalFibreEdgeEnergy (axisCentering4 fieldValue axis) axis transverse
  ≡ physicalFibreEdgeEnergy fieldValue axis transverse
axisCenteringFibreEnergyExact fieldValue axis transverse =
  sumRationalCong
    (allCyclicIndices side3)
    (λ predecessor →
      sq
        (axisCentering4 fieldValue axis
          (insertAxis axis (sucᵢ predecessor) transverse)
        - axisCentering4 fieldValue axis
          (insertAxis axis (weakenIndex predecessor) transverse)))
    (λ predecessor →
      sq
        (fieldValue (insertAxis axis (sucᵢ predecessor) transverse)
        - fieldValue (insertAxis axis (weakenIndex predecessor) transverse)))
    (λ predecessor →
      cong sq (axisCenteringEdgeDifferenceExact
        fieldValue axis transverse predecessor))

axisCenteringDirectionalEnergyExact : ∀ fieldValue axis →
  axisDirectionalEnergy axis (axisCentering4 fieldValue axis)
  ≡ axisDirectionalEnergy axis fieldValue
axisCenteringDirectionalEnergyExact fieldValue axis =
  sumRationalCong
    (physicalTransverseCoordinates side4)
    (physicalFibreEdgeEnergy (axisCentering4 fieldValue axis) axis)
    (physicalFibreEdgeEnergy fieldValue axis)
    (axisCenteringFibreEnergyExact fieldValue axis)

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

martingale0DirectionalEnergyExact : ∀ fieldValue →
  axisDirectionalEnergy zeroᵢ (martingaleField0 fieldValue)
  ≡ axisDirectionalEnergy zeroᵢ fieldValue
martingale0DirectionalEnergyExact fieldValue =
  axisCenteringDirectionalEnergyExact fieldValue zeroᵢ

martingale1DirectionalEnergyBelow : ∀ fieldValue →
  axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) fieldValue
martingale1DirectionalEnergyBelow fieldValue =
  subst
    (λ left → left ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) fieldValue)
    (sym (axisCenteringDirectionalEnergyExact
      (average0 fieldValue) (sucᵢ zeroᵢ)))
    (distinctAxisDirectionalEnergyContraction
      zeroᵢ (sucᵢ zeroᵢ) fieldValue axis0≢axis1)

martingale2DirectionalEnergyBelow : ∀ fieldValue →
  axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) (martingaleField2 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fieldValue
martingale2DirectionalEnergyBelow fieldValue =
  subst
    (λ left → left ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fieldValue)
    (sym (axisCenteringDirectionalEnergyExact
      (average01 fieldValue) (sucᵢ (sucᵢ zeroᵢ))))
    (ℚP.≤-trans
      (distinctAxisDirectionalEnergyContraction
        (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
        (average0 fieldValue) axis1≢axis2)
      (distinctAxisDirectionalEnergyContraction
        zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) fieldValue axis0≢axis2))

martingale3DirectionalEnergyBelow : ∀ fieldValue →
  axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 fieldValue)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fieldValue
martingale3DirectionalEnergyBelow fieldValue =
  subst
    (λ left →
      left ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fieldValue)
    (sym (axisCenteringDirectionalEnergyExact
      (average012 fieldValue) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))))
    (ℚP.≤-trans
      (distinctAxisDirectionalEnergyContraction
        (sucᵢ (sucᵢ zeroᵢ))
        (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
        (average01 fieldValue) axis2≢axis3)
      (ℚP.≤-trans
        (distinctAxisDirectionalEnergyContraction
          (sucᵢ zeroᵢ)
          (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          (average0 fieldValue) axis1≢axis3)
        (distinctAxisDirectionalEnergyContraction
          zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          fieldValue axis0≢axis3)))

globalDirectionalEnergy : SiteField side4 → ℚ
globalDirectionalEnergy fieldValue =
  axisDirectionalEnergy zeroᵢ fieldValue
  + (axisDirectionalEnergy (sucᵢ zeroᵢ) fieldValue
  + (axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) fieldValue
  + axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fieldValue))

path4MartingaleDirectionalEnergyContraction : ∀ fieldValue →
  martingaleDirectionalEnergySum fieldValue ≤ globalDirectionalEnergy fieldValue
path4MartingaleDirectionalEnergyContraction fieldValue =
  ℚP.+-mono-≤
    (subst
      (λ value → value ≤ axisDirectionalEnergy zeroᵢ fieldValue)
      (sym (martingale0DirectionalEnergyExact fieldValue))
      ℚP.≤-refl)
    (ℚP.+-mono-≤
      (martingale1DirectionalEnergyBelow fieldValue)
      (ℚP.+-mono-≤
        (martingale2DirectionalEnergyBelow fieldValue)
        (martingale3DirectionalEnergyBelow fieldValue)))

path4GlobalPoincare : ∀ fieldValue → GlobalMeanZero4 fieldValue →
  oneSixteenth * globalNormSq fieldValue ≤ globalDirectionalEnergy fieldValue
path4GlobalPoincare fieldValue meanZero =
  ℚP.≤-trans
    (path4MartingalePoincareBeforeEnergyContraction fieldValue meanZero)
    (path4MartingaleDirectionalEnergyContraction fieldValue)

path4AxisCenteringEnergyIdentityLevel : ProofLevel
path4AxisCenteringEnergyIdentityLevel = machineChecked

path4MartingaleDirectionalEnergyContractionLevel : ProofLevel
path4MartingaleDirectionalEnergyContractionLevel = machineChecked

path4GlobalPoincareLevel : ProofLevel
path4GlobalPoincareLevel = machineChecked
