module DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
  using (SiteField; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
  using (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
  using (globalBlockInner)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
  using (FieldEqual; subtractField)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
  using (addField; globalNormSq; globalNormRespectsPointwise)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (RationalBondField4; bondComponent; bondNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (physicalTangentInner)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact

------------------------------------------------------------------------
-- Exact Pythagoras for the orthogonal block projection Q*Q.
------------------------------------------------------------------------

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

squareAddExpandRaw : ∀ a b →
  (a + b) * (a + b) ≡ a * a + (twoℚ * (a * b) + b * b)
squareAddExpandRaw = ℚRing.solve-∀

globalNormAddExpansion : (left right : SiteField side4) →
  globalNormSq (addField left right)
  ≡ globalNormSq left
    + (twoℚ * globalBlockInner left right + globalNormSq right)
globalNormAddExpansion left right =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site →
        (left site + right site) * (left site + right site))
      (λ site →
        left site * left site
        + (twoℚ * (left site * right site) + right site * right site))
      (λ site → squareAddExpandRaw (left site) (right site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site → left site * left site)
        (λ site →
          twoℚ * (left site * right site) + right site * right site))
      (cong
        (_+_ (globalNormSq left))
        (trans
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → twoℚ * (left site * right site))
            (λ site → right site * right site))
          (cong
            (λ u → u + globalNormSq right)
            (sumRationalScale twoℚ (physicalBlockSites side4)
              (λ site → left site * right site))))))

scalarProjectionReconstruction : (fld : SiteField side4) →
  FieldEqual
    (addField
      (subtractField fld (average0123 fld))
      (average0123 fld))
    fld
scalarProjectionReconstruction fld site =
  subAddCancelRaw (fld site) (average0123 fld site)

dropTwoZeroCrossRaw : ∀ a b → a + (twoℚ * 0ℚ + b) ≡ a + b
dropTwoZeroCrossRaw = ℚRing.solve-∀

scalarProjectionPythagoras : (fld : SiteField side4) →
  globalNormSq fld
  ≡ globalNormSq (subtractField fld (average0123 fld))
    + globalNormSq (average0123 fld)
scalarProjectionPythagoras fld =
  trans
    (sym (globalNormRespectsPointwise (scalarProjectionReconstruction fld)))
    (trans
      (globalNormAddExpansion
        (subtractField fld (average0123 fld))
        (average0123 fld))
      (trans
        (cong
          (λ cross →
            globalNormSq (subtractField fld (average0123 fld))
            + (twoℚ * cross + globalNormSq (average0123 fld)))
          (average0123ResidualOrthogonal
            fld (average0123 fld) (average0123Fixed fld)))
        (dropTwoZeroCrossRaw
          (globalNormSq (subtractField fld (average0123 fld)))
          (globalNormSq (average0123 fld)))))

bondProjection : RationalBondField4 → RationalBondField4
bondProjection = scalarBlockProjection

bondFluctuation : RationalBondField4 → RationalBondField4
bondFluctuation fld bond = fld bond - bondProjection fld bond

bondProjectionPythagoras : (fld : RationalBondField4) →
  bondNormSq fld
  ≡ bondNormSq (bondFluctuation fld) + bondNormSq (bondProjection fld)
bondProjectionPythagoras fld =
  trans
    (sumRationalCong
      (allCyclicIndices four)
      (λ bondAxis → globalNormSq (bondComponent fld bondAxis))
      (λ bondAxis →
        globalNormSq
          (subtractField (bondComponent fld bondAxis)
            (average0123 (bondComponent fld bondAxis)))
        + globalNormSq (average0123 (bondComponent fld bondAxis)))
      (λ bondAxis → scalarProjectionPythagoras (bondComponent fld bondAxis)))
    (sumRationalAdd
      (allCyclicIndices four)
      (λ bondAxis →
        globalNormSq
          (subtractField (bondComponent fld bondAxis)
            (average0123 (bondComponent fld bondAxis))))
      (λ bondAxis →
        globalNormSq (average0123 (bondComponent fld bondAxis))))

threePairRearrangeRaw : ∀ a1 b1 a2 b2 a3 b3 →
  (a1 + b1) + ((a2 + b2) + (a3 + b3)) ≡ (a1 + (a2 + a3)) + (b1 + (b2 + b3))
threePairRearrangeRaw = ℚRing.solve-∀

addCommRaw : ∀ a b → a + b ≡ b + a
addCommRaw = ℚRing.solve-∀

scaleAddRaw : ∀ c a b → c * (a + b) ≡ c * a + c * b
scaleAddRaw = ℚRing.solve-∀

physicalNormProjectionPythagoras : ∀ tangent →
  physicalUnweightedNormSq tangent
  ≡ physicalUnweightedNormSq (fineFluctuation tangent)
    + physicalUnweightedNormSq (fineProjection tangent)
physicalNormProjectionPythagoras tangent =
  trans
    (cong₂ _+_
      (bondProjectionPythagoras (tangent component1))
      (cong₂ _+_
        (bondProjectionPythagoras (tangent component2))
        (bondProjectionPythagoras (tangent component3))))
    (threePairRearrangeRaw
      (bondNormSq (bondFluctuation (tangent component1)))
      (bondNormSq (bondProjection (tangent component1)))
      (bondNormSq (bondFluctuation (tangent component2)))
      (bondNormSq (bondProjection (tangent component2)))
      (bondNormSq (bondFluctuation (tangent component3)))
      (bondNormSq (bondProjection (tangent component3))))

coarseFineNormSqExact : ∀ tangent →
  physicalUnweightedNormSq tangent
  ≡ physicalUnweightedNormSq (fineProjection tangent)
    + physicalUnweightedNormSq (fineFluctuation tangent)
coarseFineNormSqExact tangent =
  trans
    (physicalNormProjectionPythagoras tangent)
    (addCommRaw
      (physicalUnweightedNormSq (fineFluctuation tangent))
      (physicalUnweightedNormSq (fineProjection tangent)))

physicalNormMatchesInner : ∀ tangent →
  physicalUnweightedNormSq tangent ≡ physicalTangentInner tangent tangent
physicalNormMatchesInner tangent = refl

coarsePenaltyNormMatchesProjection : ∀ tangent →
  concreteCoarseInner
    (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
  ≡ physicalUnweightedNormSq (fineProjection tangent)
coarsePenaltyNormMatchesProjection tangent =
  sym (physicalNormMatchesInner (fineProjection tangent))

------------------------------------------------------------------------
-- Ordered assembly.  The only order inputs are exactly the two physical lower
-- bounds: the fluctuation Hessian estimate and domination of the scaled coarse
-- norm by the Q penalty.  No equality or orthogonality is left abstract.
------------------------------------------------------------------------

coarsePenalizedCoercivity :
  ∀ tangent fluctuationEnergy →
  configuredPathCoercivityConstant
      * physicalUnweightedNormSq (fineFluctuation tangent)
    ≤ fluctuationEnergy →
  configuredPathCoercivityConstant
      * physicalUnweightedNormSq (fineProjection tangent)
    ≤ concreteCoarseInner
        (literalBlockAverageQ tangent) (literalBlockAverageQ tangent) →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ fluctuationEnergy
    + concreteCoarseInner
        (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
coarsePenalizedCoercivity tangent fluctuationEnergy fineLower coarseLower =
  subst
    (λ left →
      left ≤ fluctuationEnergy
        + concreteCoarseInner
            (literalBlockAverageQ tangent) (literalBlockAverageQ tangent))
    (sym (scaleSplitting tangent))
    (ℚP.+-mono-≤ fineLower coarseLower)
  where
  scaleSplitting : ∀ current →
    configuredPathCoercivityConstant * physicalUnweightedNormSq current
    ≡ configuredPathCoercivityConstant
        * physicalUnweightedNormSq (fineFluctuation current)
      + configuredPathCoercivityConstant
        * physicalUnweightedNormSq (fineProjection current)
  scaleSplitting current =
    trans
      (cong (_*_ configuredPathCoercivityConstant)
        (physicalNormProjectionPythagoras current))
      (scaleAddRaw
        configuredPathCoercivityConstant
        (physicalUnweightedNormSq (fineFluctuation current))
        (physicalUnweightedNormSq (fineProjection current)))

concreteCoarseFineNormSplittingLevel : ProofLevel
concreteCoarseFineNormSplittingLevel = machineChecked

concreteCoarseFinePythagorasLevel : ProofLevel
concreteCoarseFinePythagorasLevel = machineChecked

coarsePenalizedCoercivityAssemblyLevel : ProofLevel
coarsePenalizedCoercivityAssemblyLevel = machineChecked

coarsePenaltyScalarDominationLevel : ProofLevel
coarsePenaltyScalarDominationLevel = conditional
