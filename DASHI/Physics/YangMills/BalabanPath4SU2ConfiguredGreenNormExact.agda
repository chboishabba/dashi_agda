module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenNormExact where

open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalScale)
import DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact as SumLift
import DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact as OpaqueAlgebra
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
  using (globalNormSq)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (bondComponent; bondNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenNormExact
  using (sixteen; scalarGreenNormBound)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact
  using (configuredPhysicalGreen)

------------------------------------------------------------------------
-- Once scalar Green bounds have been proved on each axis/component fibre, the
-- global configured norm stays above that boundary: finite summation uses the
-- relation-preserving observer and the final three-component scaling is an
-- opaque rational identity.  No reflection sees the physical tangent carrier.
------------------------------------------------------------------------

configuredGreenBondNormBound : ∀ source component →
  bondNormSq (configuredPhysicalGreen source component)
  ≤ sixteen * bondNormSq (source component)
configuredGreenBondNormBound source component =
  trans
    (SumLift.sumRationalMonotoneViaFibre
      (allCyclicIndices four)
      (λ axis → globalNormSq
        (bondComponent (configuredPhysicalGreen source component) axis))
      (λ axis → sixteen * globalNormSq
        (bondComponent (source component) axis))
      (λ axis → scalarGreenNormBound
        (bondComponent (source component) axis)))
    (sumRationalScale sixteen (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent (source component) axis)))

configuredPhysicalGreenNormBound : ∀ source →
  physicalUnweightedNormSq (configuredPhysicalGreen source)
  ≤ sixteen * physicalUnweightedNormSq source
configuredPhysicalGreenNormBound source =
  subst
    (λ upper →
      physicalUnweightedNormSq (configuredPhysicalGreen source) ≤ upper)
    (sym
      (OpaqueAlgebra.scaleThreeSum
        sixteen
        (bondNormSq (source component1))
        (bondNormSq (source component2))
        (bondNormSq (source component3))))
    (ℚP.+-mono-≤
      (configuredGreenBondNormBound source component1)
      (ℚP.+-mono-≤
        (configuredGreenBondNormBound source component2)
        (configuredGreenBondNormBound source component3)))

configuredPhysicalGreenNormLevel : ProofLevel
configuredPhysicalGreenNormLevel = machineChecked
