module DASHI.Physics.YangMills.BalabanPath4SU2LiteralWilsonOperatorRieszExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using (sumSwap)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (siteSum4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4; scalarBondInner)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
  using (componentCurlEnergy; curlPlaneEnergy)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  (literalDiscreteCurlEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (componentScalarBondField; physicalTangentInner; literalCurlEnergyComponentFold)

scalarWilsonOperatorPairingExact : (fld : ScalarBondField4) →
  scalarBondInner fld (scalarWilsonOperator fld)
  ≡ componentCurlEnergy fld
scalarWilsonOperatorPairingExact fld =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis → siteSum4 (λ site → fld axis site * scalarWilsonOperator fld axis site))
      (λ axis → sumRational positivePlaquettePlanes4 (λ plane → siteSum4 (λ site → fld axis site * planeWilsonContribution plane fld axis site)))
      (λ axis →
        trans
          (sumRationalCong (physicalBlockSites side4)
            (λ site → fld axis site * scalarWilsonOperator fld axis site)
            (λ site → sumRational positivePlaquettePlanes4 (λ plane → fld axis site * planeWilsonContribution plane fld axis site))
            (λ site →
              sym (sumRationalScale (fld axis site)
                positivePlaquettePlanes4
                (λ plane → planeWilsonContribution plane fld axis site))))
          (sumSwap (physicalBlockSites side4) positivePlaquettePlanes4
            (λ site plane → fld axis site
              * planeWilsonContribution plane fld axis site))))
    (trans
      (sumSwap (allCyclicIndices four) positivePlaquettePlanes4
        (λ axis plane → siteSum4 (λ site →
          fld axis site * planeWilsonContribution plane fld axis site)))
      (sumRationalCong positivePlaquettePlanes4
        (λ plane → sumRational (allCyclicIndices four) (λ axis → siteSum4 (λ site → fld axis site * planeWilsonContribution plane fld axis site)))
        (λ plane → curlPlaneEnergy plane fld)
        (λ plane → scalarPlanePairingExact plane fld)))

literalWilsonOperator : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
literalWilsonOperator tangent component (pair site axis) =
  scalarWilsonOperator (componentScalarBondField tangent component) axis site

physicalWilsonOperatorPairingExact : ∀ tangent →
  physicalTangentInner tangent (literalWilsonOperator tangent)
  ≡ literalDiscreteCurlEnergy tangent
physicalWilsonOperatorPairingExact tangent =
  trans
    (cong₂ _+_
      (scalarWilsonOperatorPairingExact
        (componentScalarBondField tangent component1))
      (cong₂ _+_
        (scalarWilsonOperatorPairingExact
          (componentScalarBondField tangent component2))
        (scalarWilsonOperatorPairingExact
          (componentScalarBondField tangent component3))))
    (sym (literalCurlEnergyComponentFold tangent))

literalWilsonOperatorRieszLevel : ProofLevel
literalWilsonOperatorRieszLevel = machineChecked
