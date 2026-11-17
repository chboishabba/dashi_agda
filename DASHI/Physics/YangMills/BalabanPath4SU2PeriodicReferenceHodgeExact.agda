module DASHI.Physics.YangMills.BalabanPath4SU2PeriodicReferenceHodgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (allCyclicIndices; four; zeroᵢ)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (insertAxis; physicalTransverseCoordinates)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact
  using
    ( literalWilsonHessianPositivePlaneFold
    ; literalWilsonHessianEqualsCurlEnergy
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using
    ( componentScalarBondField
    ; literalGaugeFixingEnergy
    ; physicalPeriodicReferenceDifferenceEnergy
    ; discreteCurlDivergenceHodgeIdentity
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ sumRational values term
sumRationalNonnegative [] term pointwise = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term pointwise =
  subst
    (λ left → left ≤ term value + sumRational values term)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (pointwise value)
      (sumRationalNonnegative values term pointwise))

periodicWrapFibreEnergyNonnegative : ∀ fld axis transverse →
  0ℚ ≤ periodicWrapFibreEnergy fld axis transverse
periodicWrapFibreEnergyNonnegative fld axis transverse =
  squareNonnegative
    (fld (insertAxis axis zeroᵢ transverse)
      - fld (insertAxis axis last4 transverse))

periodicWrapEnergyNonnegative : ∀ axis fld →
  0ℚ ≤ periodicWrapEnergy axis fld
periodicWrapEnergyNonnegative axis fld =
  sumRationalNonnegative
    (physicalTransverseCoordinates side4)
    (periodicWrapFibreEnergy fld axis)
    (periodicWrapFibreEnergyNonnegative fld axis)

componentPeriodicWrapEnergyNonnegative : ∀ fld →
  0ℚ ≤ componentPeriodicWrapEnergy fld
componentPeriodicWrapEnergyNonnegative fld =
  sumRationalNonnegative
    (allCyclicIndices four)
    (λ componentAxis →
      sumRational (allCyclicIndices four) (λ derivativeAxis →
        periodicWrapEnergy derivativeAxis (fld componentAxis)))
    (λ componentAxis →
      sumRationalNonnegative
        (allCyclicIndices four)
        (λ derivativeAxis →
          periodicWrapEnergy derivativeAxis (fld componentAxis))
        (λ derivativeAxis →
          periodicWrapEnergyNonnegative derivativeAxis
            (fld componentAxis)))

physicalPeriodicWrapEnergyNonnegative : ∀ tangent →
  0ℚ ≤ physicalPeriodicWrapEnergy tangent
physicalPeriodicWrapEnergyNonnegative tangent =
  subst
    (λ left → left ≤
      componentPeriodicWrapEnergy (componentScalarBondField tangent component1)
      + (componentPeriodicWrapEnergy
          (componentScalarBondField tangent component2)
      + componentPeriodicWrapEnergy
          (componentScalarBondField tangent component3)))
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (componentPeriodicWrapEnergyNonnegative
        (componentScalarBondField tangent component1))
      (ℚP.+-mono-≤
        (componentPeriodicWrapEnergyNonnegative
          (componentScalarBondField tangent component2))
        (componentPeriodicWrapEnergyNonnegative
          (componentScalarBondField tangent component3))))

literalWilsonGaugeEqualsPeriodicDifferenceEnergy : ∀ tangent →
  literalWilsonHessianPositivePlaneFold tangent
  + literalGaugeFixingEnergy tangent
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
literalWilsonGaugeEqualsPeriodicDifferenceEnergy tangent =
  trans
    (cong (_+ literalGaugeFixingEnergy tangent)
      (literalWilsonHessianEqualsCurlEnergy tangent))
    (discreteCurlDivergenceHodgeIdentity tangent)

physicalReferenceDifferenceBelowPeriodic : ∀ tangent →
  physicalReferenceDifferenceEnergy tangent
  ≤ physicalPeriodicReferenceDifferenceEnergy tangent
physicalReferenceDifferenceBelowPeriodic tangent =
  subst
    (λ right → physicalReferenceDifferenceEnergy tangent ≤ right)
    (sym (physicalPeriodicDifferenceOpenPlusWrap tangent))
    (baseBelowBasePlusRemainder
      (physicalReferenceDifferenceEnergy tangent)
      (physicalPeriodicWrapEnergy tangent)
      (physicalPeriodicWrapEnergyNonnegative tangent))

physicalReferenceDifferenceBelowLiteralWilsonGauge : ∀ tangent →
  physicalReferenceDifferenceEnergy tangent
  ≤ literalWilsonHessianPositivePlaneFold tangent
    + literalGaugeFixingEnergy tangent
physicalReferenceDifferenceBelowLiteralWilsonGauge tangent =
  subst
    (λ right → physicalReferenceDifferenceEnergy tangent ≤ right)
    (sym (literalWilsonGaugeEqualsPeriodicDifferenceEnergy tangent))
    (physicalReferenceDifferenceBelowPeriodic tangent)

literalPeriodicReferenceHodgeCoercivity : ∀ tangent →
  PhysicalBlockAverageZero tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ literalWilsonHessianPositivePlaneFold tangent
    + literalGaugeFixingEnergy tangent
literalPeriodicReferenceHodgeCoercivity tangent blockZero =
  ℚP.≤-trans
    (physicalBlockConstrainedDifferencePoincare tangent blockZero)
    (physicalReferenceDifferenceBelowLiteralWilsonGauge tangent)

literalGaugeFixedPeriodicHessian : PhysicalSU2Tangent4 → ℚ → ℚ
literalGaugeFixedPeriodicHessian tangent blockPenalty =
  literalWilsonHessianPositivePlaneFold tangent
  + (literalGaugeFixingEnergy tangent + blockPenalty)

literalPeriodicReferenceHodgeWithBlockPenalty :
  ∀ tangent blockPenalty →
  PhysicalBlockAverageZero tangent →
  0ℚ ≤ blockPenalty →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ literalGaugeFixedPeriodicHessian tangent blockPenalty
literalPeriodicReferenceHodgeWithBlockPenalty tangent blockPenalty blockZero
  blockPenaltyNonnegative =
  ℚP.≤-trans
    (literalPeriodicReferenceHodgeCoercivity tangent blockZero)
    (ℚP.+-mono-≤
      (ℚP.≤-refl {x = literalWilsonHessianPositivePlaneFold tangent})
      (baseBelowBasePlusRemainder
        (literalGaugeFixingEnergy tangent)
        blockPenalty
        blockPenaltyNonnegative))

literalWilsonGaugePeriodicIdentityLevel : ProofLevel
literalWilsonGaugePeriodicIdentityLevel = machineChecked

physicalPeriodicWrapNonnegativeLevel : ProofLevel
physicalPeriodicWrapNonnegativeLevel = machineChecked

literalPeriodicReferenceHodgeCoercivityLevel : ProofLevel
literalPeriodicReferenceHodgeCoercivityLevel = machineChecked
