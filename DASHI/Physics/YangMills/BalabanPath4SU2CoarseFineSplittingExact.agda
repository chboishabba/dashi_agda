module DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
  using (sumRational; sumRationalCong; sumRationalScale)
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
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact

------------------------------------------------------------------------
-- Exact Pythagoras for the orthogonal block projection Q*Q.
------------------------------------------------------------------------

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

globalNormAddExpansion : ∀ left right →
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
      (λ site → ℚRing.solve-∀ (left site) (right site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site → left site * left site)
        (λ site →
          twoℚ * (left site * right site) + right site * right site))
      (cong₂ _+_ refl
        (trans
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → twoℚ * (left site * right site))
            (λ site → right site * right site))
          (cong₂ _+_
            (sumRationalScale twoℚ (physicalBlockSites side4)
              (λ site → left site * right site))
            refl))))

scalarProjectionReconstruction : ∀ field →
  FieldEqual
    (addField
      (subtractField field (average0123 field))
      (average0123 field))
    field
scalarProjectionReconstruction field site =
  ℚRing.solve-∀ (field site) (average0123 field site)

scalarProjectionPythagoras : ∀ field →
  globalNormSq field
  ≡ globalNormSq (subtractField field (average0123 field))
    + globalNormSq (average0123 field)
scalarProjectionPythagoras field =
  trans
    (sym (globalNormRespectsPointwise (scalarProjectionReconstruction field)))
    (trans
      (globalNormAddExpansion
        (subtractField field (average0123 field))
        (average0123 field))
      (trans
        (cong
          (λ cross →
            globalNormSq (subtractField field (average0123 field))
            + (twoℚ * cross + globalNormSq (average0123 field)))
          (average0123ResidualOrthogonal
            field (average0123 field) (average0123Fixed field)))
        (ℚRing.solve-∀
          (globalNormSq (subtractField field (average0123 field)))
          (globalNormSq (average0123 field)))))

bondProjection : RationalBondField4 → RationalBondField4
bondProjection = scalarBlockProjection

bondFluctuation : RationalBondField4 → RationalBondField4
bondFluctuation field bond = field bond - bondProjection field bond

bondProjectionPythagoras : ∀ field →
  bondNormSq field
  ≡ bondNormSq (bondFluctuation field) + bondNormSq (bondProjection field)
bondProjectionPythagoras field =
  trans
    (sumRationalCong
      (allCyclicIndices four)
      (λ bondAxis → globalNormSq (bondComponent field bondAxis))
      (λ bondAxis →
        globalNormSq
          (subtractField (bondComponent field bondAxis)
            (average0123 (bondComponent field bondAxis)))
        + globalNormSq (average0123 (bondComponent field bondAxis)))
      (λ bondAxis → scalarProjectionPythagoras (bondComponent field bondAxis)))
    (sumRationalAdd
      (allCyclicIndices four)
      (λ bondAxis →
        globalNormSq
          (subtractField (bondComponent field bondAxis)
            (average0123 (bondComponent field bondAxis))))
      (λ bondAxis →
        globalNormSq (average0123 (bondComponent field bondAxis))))

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
    (ℚRing.solve-∀
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
    (ℚRing.solve-∀
      (physicalUnweightedNormSq (fineFluctuation tangent))
      (physicalUnweightedNormSq (fineProjection tangent)))

physicalNormMatchesInner : ∀ tangent →
  physicalUnweightedNormSq tangent
  ≡ DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.physicalTangentInner
      tangent tangent
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
    (scaleSplitting tangent)
    (Data.Rational.Properties.+-mono-≤ fineLower coarseLower)
  where
  scaleSplitting : ∀ current →
    configuredPathCoercivityConstant * physicalUnweightedNormSq current
    ≡ configuredPathCoercivityConstant
        * physicalUnweightedNormSq (fineFluctuation current)
      + configuredPathCoercivityConstant
        * physicalUnweightedNormSq (fineProjection current)
  scaleSplitting current
    rewrite physicalNormProjectionPythagoras current =
    ℚRing.solve-∀
      configuredPathCoercivityConstant
      (physicalUnweightedNormSq (fineFluctuation current))
      (physicalUnweightedNormSq (fineProjection current))

concreteCoarseFineNormSplittingLevel : ProofLevel
concreteCoarseFineNormSplittingLevel = machineChecked

concreteCoarseFinePythagorasLevel : ProofLevel
concreteCoarseFinePythagorasLevel = machineChecked

coarsePenalizedCoercivityAssemblyLevel : ProofLevel
coarsePenalizedCoercivityAssemblyLevel = machineChecked

coarsePenaltyScalarDominationLevel : ProofLevel
coarsePenaltyScalarDominationLevel = conditional
