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
  ∀ field axis transverse predecessor →
  axisCentering4 field axis
      (insertAxis axis (sucᵢ predecessor) transverse)
  - axisCentering4 field axis
      (insertAxis axis (weakenIndex predecessor) transverse)
  ≡ field (insertAxis axis (sucᵢ predecessor) transverse)
    - field (insertAxis axis (weakenIndex predecessor) transverse)
axisCenteringEdgeDifferenceExact field axis transverse predecessor
  rewrite axisCentering4OnFibre field axis transverse (sucᵢ predecessor)
        | axisCentering4OnFibre field axis transverse (weakenIndex predecessor) =
  ℚRing.solve-∀
    (field (insertAxis axis (sucᵢ predecessor) transverse))
    (field (insertAxis axis (weakenIndex predecessor) transverse))
    (physicalFibreSum field axis transverse)

axisCenteringFibreEnergyExact : ∀ field axis transverse →
  physicalFibreEdgeEnergy (axisCentering4 field axis) axis transverse
  ≡ physicalFibreEdgeEnergy field axis transverse
axisCenteringFibreEnergyExact field axis transverse =
  sumRationalCong
    (allCyclicIndices side3)
    (λ predecessor →
      sq
        (axisCentering4 field axis
          (insertAxis axis (sucᵢ predecessor) transverse)
        - axisCentering4 field axis
          (insertAxis axis (weakenIndex predecessor) transverse)))
    (λ predecessor →
      sq
        (field (insertAxis axis (sucᵢ predecessor) transverse)
        - field (insertAxis axis (weakenIndex predecessor) transverse)))
    (λ predecessor →
      cong sq (axisCenteringEdgeDifferenceExact
        field axis transverse predecessor))

axisCenteringDirectionalEnergyExact : ∀ field axis →
  axisDirectionalEnergy axis (axisCentering4 field axis)
  ≡ axisDirectionalEnergy axis field
axisCenteringDirectionalEnergyExact field axis =
  sumRationalCong
    (physicalTransverseCoordinates side4)
    (physicalFibreEdgeEnergy (axisCentering4 field axis) axis)
    (physicalFibreEdgeEnergy field axis)
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
  axisDirectionalEnergy zeroᵢ (martingaleField0 field)
  ≡ axisDirectionalEnergy zeroᵢ field
martingale0DirectionalEnergyExact field =
  axisCenteringDirectionalEnergyExact field zeroᵢ

martingale1DirectionalEnergyBelow : ∀ field →
  axisDirectionalEnergy (sucᵢ zeroᵢ) (martingaleField1 field)
  ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) field
martingale1DirectionalEnergyBelow field =
  subst
    (λ left → left ≤ axisDirectionalEnergy (sucᵢ zeroᵢ) field)
    (sym (axisCenteringDirectionalEnergyExact
      (average0 field) (sucᵢ zeroᵢ)))
    (distinctAxisDirectionalEnergyContraction
      zeroᵢ (sucᵢ zeroᵢ) field axis0≢axis1)

martingale2DirectionalEnergyBelow : ∀ field →
  axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) (martingaleField2 field)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field
martingale2DirectionalEnergyBelow field =
  subst
    (λ left → left ≤ axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field)
    (sym (axisCenteringDirectionalEnergyExact
      (average01 field) (sucᵢ (sucᵢ zeroᵢ))))
    (ℚP.≤-trans
      (distinctAxisDirectionalEnergyContraction
        (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
        (average0 field) axis1≢axis2)
      (distinctAxisDirectionalEnergyContraction
        zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) field axis0≢axis2))

martingale3DirectionalEnergyBelow : ∀ field →
  axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 field)
  ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field
martingale3DirectionalEnergyBelow field =
  subst
    (λ left →
      left ≤ axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field)
    (sym (axisCenteringDirectionalEnergyExact
      (average012 field) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))))
    (ℚP.≤-trans
      (distinctAxisDirectionalEnergyContraction
        (sucᵢ (sucᵢ zeroᵢ))
        (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
        (average01 field) axis2≢axis3)
      (ℚP.≤-trans
        (distinctAxisDirectionalEnergyContraction
          (sucᵢ zeroᵢ)
          (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          (average0 field) axis1≢axis3)
        (distinctAxisDirectionalEnergyContraction
          zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
          field axis0≢axis3)))

globalDirectionalEnergy : SiteField side4 → ℚ
globalDirectionalEnergy field =
  axisDirectionalEnergy zeroᵢ field
  + (axisDirectionalEnergy (sucᵢ zeroᵢ) field
  + (axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field
  + axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field))

path4MartingaleDirectionalEnergyContraction : ∀ field →
  martingaleDirectionalEnergySum field ≤ globalDirectionalEnergy field
path4MartingaleDirectionalEnergyContraction field =
  ℚP.+-mono-≤
    (subst
      (λ value → value ≤ axisDirectionalEnergy zeroᵢ field)
      (sym (martingale0DirectionalEnergyExact field))
      ℚP.≤-refl)
    (ℚP.+-mono-≤
      (martingale1DirectionalEnergyBelow field)
      (ℚP.+-mono-≤
        (martingale2DirectionalEnergyBelow field)
        (martingale3DirectionalEnergyBelow field)))

path4GlobalPoincare : ∀ field → GlobalMeanZero4 field →
  oneSixteenth * globalNormSq field ≤ globalDirectionalEnergy field
path4GlobalPoincare field meanZero =
  ℚP.≤-trans
    (path4MartingalePoincareBeforeEnergyContraction field meanZero)
    (path4MartingaleDirectionalEnergyContraction field)

path4AxisCenteringEnergyIdentityLevel : ProofLevel
path4AxisCenteringEnergyIdentityLevel = machineChecked

path4MartingaleDirectionalEnergyContractionLevel : ProofLevel
path4MartingaleDirectionalEnergyContractionLevel = machineChecked

path4GlobalPoincareLevel : ProofLevel
path4GlobalPoincareLevel = machineChecked
