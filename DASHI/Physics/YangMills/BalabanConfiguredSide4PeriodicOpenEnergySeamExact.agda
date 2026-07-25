module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact using
  (axisDirectionalEnergy)
open import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact using
  (globalDirectionalEnergy)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact using
  (bondReferenceDifferenceEnergy; bondComponent)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4; axis0; axis1; axis2; axis3)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact using
  (forwardDerivativeEnergy; componentPeriodicDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (componentScalarBondField; physicalPeriodicReferenceDifferenceEnergy)

------------------------------------------------------------------------
-- The fourth edge of a periodic length-four fibre is the wrap edge 3 -> 0.
------------------------------------------------------------------------

last4 : CyclicIndex side4
last4 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

periodicWrapFibreEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
periodicWrapFibreEnergy field axis transverse =
  sq
    (field (insertAxis axis zeroᵢ transverse)
    Data.Rational._-_
    field (insertAxis axis last4 transverse))

periodicWrapEnergy : Axis4 → SiteField side4 → ℚ
periodicWrapEnergy axis field =
  sumRational (physicalTransverseCoordinates side4)
    (periodicWrapFibreEnergy field axis)

periodicFibreEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
periodicFibreEnergy field axis transverse =
  sumRational (allCyclicIndices side4) (λ coordinate →
    sq (forwardDifference4 axis field
      (insertAxis axis coordinate transverse)))

periodicFibreDifferenceDecomposition : ∀ field axis transverse →
  periodicFibreEnergy field axis transverse
  ≡ physicalFibreEdgeEnergy field axis transverse
    + periodicWrapFibreEnergy field axis transverse
periodicFibreDifferenceDecomposition field zeroᵢ
  (pair x1 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair zeroᵢ x1) (pair x2 x3)))
    (field (pair (pair (sucᵢ zeroᵢ) x1) (pair x2 x3)))
    (field (pair (pair (sucᵢ (sucᵢ zeroᵢ)) x1) (pair x2 x3)))
    (field (pair (pair last4 x1) (pair x2 x3)))
periodicFibreDifferenceDecomposition field (sucᵢ zeroᵢ)
  (pair x0 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 zeroᵢ) (pair x2 x3)))
    (field (pair (pair x0 (sucᵢ zeroᵢ)) (pair x2 x3)))
    (field (pair (pair x0 (sucᵢ (sucᵢ zeroᵢ))) (pair x2 x3)))
    (field (pair (pair x0 last4) (pair x2 x3)))
periodicFibreDifferenceDecomposition field (sucᵢ (sucᵢ zeroᵢ))
  (pair x0 (pair x1 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair zeroᵢ x3)))
    (field (pair (pair x0 x1) (pair (sucᵢ zeroᵢ) x3)))
    (field (pair (pair x0 x1) (pair (sucᵢ (sucᵢ zeroᵢ)) x3)))
    (field (pair (pair x0 x1) (pair last4 x3)))
periodicFibreDifferenceDecomposition field
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair x0 (pair x1 x2)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair x2 zeroᵢ)))
    (field (pair (pair x0 x1) (pair x2 (sucᵢ zeroᵢ))))
    (field (pair (pair x0 x1) (pair x2 (sucᵢ (sucᵢ zeroᵢ)))))
    (field (pair (pair x0 x1) (pair x2 last4)))

forwardDerivativeEnergyOpenPlusWrap : ∀ axis field →
  forwardDerivativeEnergy axis field
  ≡ axisDirectionalEnergy axis field + periodicWrapEnergy axis field
forwardDerivativeEnergyOpenPlusWrap axis field =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (forwardDifference4 axis field site))))
    (trans
      (sumRationalCong (physicalTransverseCoordinates side4) _ _
        (periodicFibreDifferenceDecomposition field axis))
      (sumRationalAdd (physicalTransverseCoordinates side4)
        (physicalFibreEdgeEnergy field axis)
        (periodicWrapFibreEnergy field axis)))

------------------------------------------------------------------------
-- Component and three-component decompositions.
------------------------------------------------------------------------

componentOpenDifferenceEnergy : ScalarBondField4 → ℚ
componentOpenDifferenceEnergy field =
  sumRational (allCyclicIndices four)
    (λ componentAxis → globalDirectionalEnergy (field componentAxis))

componentPeriodicWrapEnergy : ScalarBondField4 → ℚ
componentPeriodicWrapEnergy field =
  sumRational (allCyclicIndices four) (λ componentAxis →
    sumRational (allCyclicIndices four) (λ derivativeAxis →
      periodicWrapEnergy derivativeAxis (field componentAxis)))

componentDerivativeFoldOpenPlusWrap : ∀ field componentAxis →
  sumRational (allCyclicIndices four) (λ derivativeAxis →
    forwardDerivativeEnergy derivativeAxis (field componentAxis))
  ≡ globalDirectionalEnergy (field componentAxis)
    + sumRational (allCyclicIndices four) (λ derivativeAxis →
        periodicWrapEnergy derivativeAxis (field componentAxis))
componentDerivativeFoldOpenPlusWrap field componentAxis =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ derivativeAxis →
        forwardDerivativeEnergyOpenPlusWrap derivativeAxis
          (field componentAxis)))
    (trans
      (sumRationalAdd (allCyclicIndices four)
        (λ derivativeAxis → axisDirectionalEnergy derivativeAxis
          (field componentAxis))
        (λ derivativeAxis → periodicWrapEnergy derivativeAxis
          (field componentAxis)))
      (cong₂ _+_
        (ℚRing.solve-∀
          (axisDirectionalEnergy axis0 (field componentAxis))
          (axisDirectionalEnergy axis1 (field componentAxis))
          (axisDirectionalEnergy axis2 (field componentAxis))
          (axisDirectionalEnergy axis3 (field componentAxis)))
        refl))

componentPeriodicDifferenceOpenPlusWrap : ∀ field →
  componentPeriodicDifferenceEnergy field
  ≡ componentOpenDifferenceEnergy field + componentPeriodicWrapEnergy field
componentPeriodicDifferenceOpenPlusWrap field =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (componentDerivativeFoldOpenPlusWrap field))
    (sumRationalAdd (allCyclicIndices four)
      (λ componentAxis → globalDirectionalEnergy (field componentAxis))
      (λ componentAxis → sumRational (allCyclicIndices four)
        (λ derivativeAxis → periodicWrapEnergy derivativeAxis
          (field componentAxis))))

componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy : ∀ field →
  componentOpenDifferenceEnergy field ≡ bondReferenceDifferenceEnergy field
componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy field = refl

physicalPeriodicWrapEnergy : PhysicalSU2Tangent4 → ℚ
physicalPeriodicWrapEnergy tangent =
  componentPeriodicWrapEnergy (componentScalarBondField tangent component1)
  + (componentPeriodicWrapEnergy (componentScalarBondField tangent component2)
  + componentPeriodicWrapEnergy (componentScalarBondField tangent component3))

physicalPeriodicDifferenceOpenPlusWrap : ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
    + physicalPeriodicWrapEnergy tangent
physicalPeriodicDifferenceOpenPlusWrap tangent =
  trans
    (cong₂ _+_
      (componentPeriodicDifferenceOpenPlusWrap
        (componentScalarBondField tangent component1))
      (cong₂ _+_
        (componentPeriodicDifferenceOpenPlusWrap
          (componentScalarBondField tangent component2))
        (componentPeriodicDifferenceOpenPlusWrap
          (componentScalarBondField tangent component3))))
    (ℚRing.solve-∀
      (bondReferenceDifferenceEnergy (tangent component1))
      (bondReferenceDifferenceEnergy (tangent component2))
      (bondReferenceDifferenceEnergy (tangent component3))
      (componentPeriodicWrapEnergy
        (componentScalarBondField tangent component1))
      (componentPeriodicWrapEnergy
        (componentScalarBondField tangent component2))
      (componentPeriodicWrapEnergy
        (componentScalarBondField tangent component3)))

hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyPlusWrap : ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent + physicalPeriodicWrapEnergy tangent
hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyPlusWrap =
  physicalPeriodicDifferenceOpenPlusWrap

hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergy : ∀ tangent →
  physicalPeriodicWrapEnergy tangent ≡ 0ℚ →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergy tangent wrapZero =
  trans
    (physicalPeriodicDifferenceOpenPlusWrap tangent)
    (trans
      (cong₂ _+_ refl wrapZero)
      (ℚRing.solve-∀ (physicalReferenceDifferenceEnergy tangent)))

periodicOpenEnergySeamLevel : ProofLevel
periodicOpenEnergySeamLevel = machineChecked

unconditionalPeriodicEqualsOpenDifferenceEnergyLevel : ProofLevel
unconditionalPeriodicEqualsOpenDifferenceEnergyLevel = conditional
