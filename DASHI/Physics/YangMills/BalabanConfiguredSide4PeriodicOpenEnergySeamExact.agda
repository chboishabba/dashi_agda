module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

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
  (RationalBondField4; bondComponent; bondReferenceDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4; axis0; axis1; axis2; axis3)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact using
  (forwardDerivativeEnergy; componentPeriodicDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (componentScalarBondField; physicalPeriodicReferenceDifferenceEnergy)

last4 : CyclicIndex side4
last4 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

periodicWrapFibreEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
periodicWrapFibreEnergy fld axis transverse =
  sq
    (fld (insertAxis axis zeroᵢ transverse)
    - fld (insertAxis axis last4 transverse))

periodicWrapEnergy : Axis4 → SiteField side4 → ℚ
periodicWrapEnergy axis fld =
  sumRational (physicalTransverseCoordinates side4)
    (periodicWrapFibreEnergy fld axis)

periodicFibreEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
periodicFibreEnergy fld axis transverse =
  sumRational (allCyclicIndices side4) (λ coordinate →
    sq (forwardDifference4 axis fld
      (insertAxis axis coordinate transverse)))

fibreFourSplitRaw : ∀ s0 s1 s2 s3 →
  s0 + (s1 + (s2 + (s3 + 0ℚ))) ≡ (s0 + (s1 + (s2 + 0ℚ))) + s3
fibreFourSplitRaw = ℚRing.solve-∀

fibreFourSplitOnAxis : ∀ fld axis transverse →
  let c0 = zeroᵢ
      c1 = sucᵢ zeroᵢ
      c2 = sucᵢ (sucᵢ zeroᵢ)
      c3 = last4
      s = λ c → sq (forwardDifference4 axis fld (insertAxis axis c transverse))
  in
  s c0 + (s c1 + (s c2 + (s c3 + 0ℚ)))
  ≡ (s c0 + (s c1 + (s c2 + 0ℚ))) + s c3
fibreFourSplitOnAxis fld axis transverse =
  let c0 = zeroᵢ
      c1 = sucᵢ zeroᵢ
      c2 = sucᵢ (sucᵢ zeroᵢ)
      c3 = last4
      s = λ c → sq (forwardDifference4 axis fld (insertAxis axis c transverse))
  in
  fibreFourSplitRaw (s c0) (s c1) (s c2) (s c3)

periodicFibreDifferenceDecomposition : ∀ fld axis transverse →
  periodicFibreEnergy fld axis transverse
  ≡ physicalFibreEdgeEnergy fld axis transverse
    + periodicWrapFibreEnergy fld axis transverse
periodicFibreDifferenceDecomposition fld zeroᵢ
  (pair x1 (pair x2 x3)) =
  fibreFourSplitOnAxis fld zeroᵢ (pair x1 (pair x2 x3))
periodicFibreDifferenceDecomposition fld (sucᵢ zeroᵢ)
  (pair x0 (pair x2 x3)) =
  fibreFourSplitOnAxis fld (sucᵢ zeroᵢ) (pair x0 (pair x2 x3))
periodicFibreDifferenceDecomposition fld (sucᵢ (sucᵢ zeroᵢ))
  (pair x0 (pair x1 x3)) =
  fibreFourSplitOnAxis fld (sucᵢ (sucᵢ zeroᵢ)) (pair x0 (pair x1 x3))
periodicFibreDifferenceDecomposition fld
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair x0 (pair x1 x2)) =
  fibreFourSplitOnAxis fld (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair x0 (pair x1 x2))

forwardDerivativeEnergyOpenPlusWrap : (axis : Axis4) (fld : SiteField side4) →
  forwardDerivativeEnergy axis fld
  ≡ axisDirectionalEnergy axis fld + periodicWrapEnergy axis fld
forwardDerivativeEnergyOpenPlusWrap axis fld =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (forwardDifference4 axis fld site))))
    (trans
      (sumRationalCong (physicalTransverseCoordinates side4)
        (periodicFibreEnergy fld axis)
        (λ transverse →
          physicalFibreEdgeEnergy fld axis transverse
          + periodicWrapFibreEnergy fld axis transverse)
        (periodicFibreDifferenceDecomposition fld axis))
      (sumRationalAdd (physicalTransverseCoordinates side4)
        (physicalFibreEdgeEnergy fld axis)
        (periodicWrapFibreEnergy fld axis)))

componentOpenDifferenceEnergy : ScalarBondField4 → ℚ
componentOpenDifferenceEnergy fld =
  sumRational (allCyclicIndices four)
    (λ componentAxis → globalDirectionalEnergy (fld componentAxis))

componentPeriodicWrapEnergy : ScalarBondField4 → ℚ
componentPeriodicWrapEnergy fld =
  sumRational (allCyclicIndices four) (λ componentAxis →
    sumRational (allCyclicIndices four) (λ derivativeAxis →
      periodicWrapEnergy derivativeAxis (fld componentAxis)))

dropZeroFourRaw : ∀ e0 e1 e2 e3 →
  e0 + (e1 + (e2 + (e3 + 0ℚ))) ≡ e0 + (e1 + (e2 + e3))
dropZeroFourRaw = ℚRing.solve-∀

componentDerivativeFoldOpenPlusWrap : (fld : ScalarBondField4) (componentAxis : Axis4) →
  sumRational (allCyclicIndices four) (λ derivativeAxis →
    forwardDerivativeEnergy derivativeAxis (fld componentAxis))
  ≡ globalDirectionalEnergy (fld componentAxis)
    + sumRational (allCyclicIndices four) (λ derivativeAxis →
        periodicWrapEnergy derivativeAxis (fld componentAxis))
componentDerivativeFoldOpenPlusWrap fld componentAxis =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ derivativeAxis → forwardDerivativeEnergy derivativeAxis (fld componentAxis))
      (λ derivativeAxis →
        axisDirectionalEnergy derivativeAxis (fld componentAxis)
        + periodicWrapEnergy derivativeAxis (fld componentAxis))
      (λ derivativeAxis →
        forwardDerivativeEnergyOpenPlusWrap derivativeAxis
          (fld componentAxis)))
    (trans
      (sumRationalAdd (allCyclicIndices four)
        (λ derivativeAxis → axisDirectionalEnergy derivativeAxis
          (fld componentAxis))
        (λ derivativeAxis → periodicWrapEnergy derivativeAxis
          (fld componentAxis)))
      (cong (_+ sumRational (allCyclicIndices four)
        (λ derivativeAxis → periodicWrapEnergy derivativeAxis (fld componentAxis)))
        (dropZeroFourRaw
          (axisDirectionalEnergy axis0 (fld componentAxis))
          (axisDirectionalEnergy axis1 (fld componentAxis))
          (axisDirectionalEnergy axis2 (fld componentAxis))
          (axisDirectionalEnergy axis3 (fld componentAxis)))))

componentPeriodicDifferenceOpenPlusWrap : (fld : ScalarBondField4) →
  componentPeriodicDifferenceEnergy fld
  ≡ componentOpenDifferenceEnergy fld + componentPeriodicWrapEnergy fld
componentPeriodicDifferenceOpenPlusWrap fld =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ componentAxis → sumRational (allCyclicIndices four)
        (λ derivativeAxis → forwardDerivativeEnergy derivativeAxis (fld componentAxis)))
      (λ componentAxis →
        globalDirectionalEnergy (fld componentAxis)
        + sumRational (allCyclicIndices four)
            (λ derivativeAxis → periodicWrapEnergy derivativeAxis (fld componentAxis)))
      (componentDerivativeFoldOpenPlusWrap fld))
    (sumRationalAdd (allCyclicIndices four)
      (λ componentAxis → globalDirectionalEnergy (fld componentAxis))
      (λ componentAxis → sumRational (allCyclicIndices four)
        (λ derivativeAxis → periodicWrapEnergy derivativeAxis
          (fld componentAxis))))

componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy : (fld : RationalBondField4) →
  componentOpenDifferenceEnergy (bondComponent fld) ≡ bondReferenceDifferenceEnergy fld
componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy fld = refl

physicalPeriodicWrapEnergy : PhysicalSU2Tangent4 → ℚ
physicalPeriodicWrapEnergy tangent =
  componentPeriodicWrapEnergy (componentScalarBondField tangent component1)
  + (componentPeriodicWrapEnergy (componentScalarBondField tangent component2)
  + componentPeriodicWrapEnergy (componentScalarBondField tangent component3))

unpairThreeRaw : ∀ a1 b1 a2 b2 a3 b3 →
  (a1 + b1) + ((a2 + b2) + (a3 + b3)) ≡ (a1 + (a2 + a3)) + (b1 + (b2 + b3))
unpairThreeRaw = ℚRing.solve-∀

addZeroRightRaw : ∀ x → x + 0ℚ ≡ x
addZeroRightRaw = ℚRing.solve-∀

physicalPeriodicDifferenceOpenPlusWrap : ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
    + physicalPeriodicWrapEnergy tangent
physicalPeriodicDifferenceOpenPlusWrap tangent =
  let f1 = componentScalarBondField tangent component1
      f2 = componentScalarBondField tangent component2
      f3 = componentScalarBondField tangent component3
  in
  trans
    (cong₂ _+_
      (componentPeriodicDifferenceOpenPlusWrap f1)
      (cong₂ _+_
        (componentPeriodicDifferenceOpenPlusWrap f2)
        (componentPeriodicDifferenceOpenPlusWrap f3)))
    (unpairThreeRaw
      (componentOpenDifferenceEnergy f1)
      (componentPeriodicWrapEnergy f1)
      (componentOpenDifferenceEnergy f2)
      (componentPeriodicWrapEnergy f2)
      (componentOpenDifferenceEnergy f3)
      (componentPeriodicWrapEnergy f3))

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
      (cong (physicalReferenceDifferenceEnergy tangent +_) wrapZero)
      (addZeroRightRaw (physicalReferenceDifferenceEnergy tangent)))

periodicOpenEnergySeamLevel : ProofLevel
periodicOpenEnergySeamLevel = machineChecked

unconditionalPeriodicEqualsOpenDifferenceEnergyLevel : ProofLevel
unconditionalPeriodicEqualsOpenDifferenceEnergyLevel = conditional
