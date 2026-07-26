module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenNormExact where

open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact
  using (sumRationalMonotone)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (bondComponent; bondNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenNormExact
  using (sixteen; scalarGreenNormBound)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact
  using (configuredPhysicalGreen)

configuredGreenBondNormBound : ∀ source component →
  bondNormSq (configuredPhysicalGreen source component)
  ≤ sixteen * bondNormSq (source component)
configuredGreenBondNormBound source component =
  trans
    (sumRationalMonotone
      (allCyclicIndices four)
      (λ axis →
        DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact.globalNormSq
          (bondComponent (configuredPhysicalGreen source component) axis))
      (λ axis → sixteen *
        DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact.globalNormSq
          (bondComponent (source component) axis))
      (λ axis → scalarGreenNormBound
        (bondComponent (source component) axis)))
    (sumRationalScale sixteen (allCyclicIndices four)
      (λ axis →
        DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact.globalNormSq
          (bondComponent (source component) axis)))

configuredPhysicalGreenNormBound : ∀ source →
  physicalUnweightedNormSq (configuredPhysicalGreen source)
  ≤ sixteen * physicalUnweightedNormSq source
configuredPhysicalGreenNormBound source =
  trans
    (ℚP.+-mono-≤
      (configuredGreenBondNormBound source component1)
      (ℚP.+-mono-≤
        (configuredGreenBondNormBound source component2)
        (configuredGreenBondNormBound source component3)))
    (ℚRing.solve-∀
      (bondNormSq (source component1))
      (bondNormSq (source component2))
      (bondNormSq (source component3)))

configuredPhysicalGreenNormLevel : ProofLevel
configuredPhysicalGreenNormLevel = machineChecked
