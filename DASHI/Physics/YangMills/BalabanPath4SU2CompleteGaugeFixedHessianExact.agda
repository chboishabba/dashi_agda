module DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (allCyclicIndices; four)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalZero)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (physicalTangentInner)
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  (literalWilsonHessianPositivePlaneFold; literalWilsonHessianEqualsCurlEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralWilsonOperatorRieszExact
  using (literalWilsonOperator; physicalWilsonOperatorPairingExact)
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralDivergenceHessianInstanceExact
  using
    ( LiteralNonDivergenceHessianData
    ; literalGaugeFixedHessianQuadraticData
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralGaugeFixedHessianAdapterExact
  using
    ( Path4SU2LiteralWilsonOperatorMatch
    ; literalConcreteDivergenceGaugeFixedDecompositionExact
    ; uniformReferenceHodgeCoercivityFromConcreteDivergence
    )

------------------------------------------------------------------------
-- The block map and its adjoint are independent of the Wilson/divergence proof.
------------------------------------------------------------------------

record LiteralCoarseBlockData (Coarse : Set) : Set₁ where
  field
    averageOperator : PhysicalSU2Tangent4 → Coarse
    averageAdjointOperator : Coarse → PhysicalSU2Tangent4
    innerCoarseOperator : Coarse → Coarse → ℚ
    coarseZeroOperator : Coarse

    averageAdjointExact : ∀ fine coarse →
      physicalTangentInner fine (averageAdjointOperator coarse)
      ≡ innerCoarseOperator (averageOperator fine) coarse

    innerCoarseZeroExact :
      innerCoarseOperator coarseZeroOperator coarseZeroOperator ≡ 0ℚ

    coarseNormNonnegativeExact : ∀ coarse →
      0ℚ ≤ innerCoarseOperator coarse coarse

zeroPhysicalSU2Tangent4 : PhysicalSU2Tangent4
zeroPhysicalSU2Tangent4 component axisSite = 0ℚ

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ sumRational values term
sumRationalNonnegative [] term termNonnegative = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term termNonnegative =
  ℚP.+-mono-≤
    (termNonnegative value)
    (sumRationalNonnegative values term termNonnegative)

scalarBondInnerZeroRight : ∀ tangent →
  physicalTangentInner tangent zeroPhysicalSU2Tangent4 ≡ 0ℚ
scalarBondInnerZeroRight tangent =
  trans
    (cong₂ _+_
      (bondInnerZeroRight (tangent component1))
      (cong₂ _+_
        (bondInnerZeroRight (tangent component2))
        (bondInnerZeroRight (tangent component3))))
    (ℚRing.solve-∀)
  where
  bondInnerZeroRight : ∀ bondField →
    sumRational (allCyclicIndices four)
      (λ axis →
        sumRational (physicalBlockSites side4)
          (λ site → bondField axis site * 0ℚ))
    ≡ 0ℚ
  bondInnerZeroRight bondField =
    trans
      (sumRationalCong
        (allCyclicIndices four)
        (λ axis →
          sumRational (physicalBlockSites side4)
            (λ site → bondField axis site * 0ℚ))
        (λ _ → 0ℚ)
        (λ axis →
          trans
            (sumRationalCong
              (physicalBlockSites side4)
              (λ site → bondField axis site * 0ℚ)
              (λ _ → 0ℚ)
              (λ _ → ℚRing.solve-∀))
            (sumRationalZero (physicalBlockSites side4))))
      (sumRationalZero (allCyclicIndices four))

scalarBondInnerNonnegative : ∀ bondField →
  0ℚ ≤ sumRational (allCyclicIndices four)
    (λ axis →
      sumRational (physicalBlockSites side4)
        (λ site → bondField axis site * bondField axis site))
scalarBondInnerNonnegative bondField =
  sumRationalNonnegative
    (allCyclicIndices four)
    (λ axis →
      sumRational (physicalBlockSites side4)
        (λ site → bondField axis site * bondField axis site))
    (λ axis →
      sumRationalNonnegative
        (physicalBlockSites side4)
        (λ site → bondField axis site * bondField axis site)
        (λ site →
          DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact.squareNonnegative
            (bondField axis site)))

physicalTangentInnerNonnegative : ∀ tangent →
  0ℚ ≤ physicalTangentInner tangent tangent
physicalTangentInnerNonnegative tangent =
  ℚP.+-mono-≤
    (scalarBondInnerNonnegative (tangent component1))
    (ℚP.+-mono-≤
      (scalarBondInnerNonnegative (tangent component2))
      (scalarBondInnerNonnegative (tangent component3)))

canonicalLiteralCoarseBlockData : LiteralCoarseBlockData PhysicalSU2Tangent4
canonicalLiteralCoarseBlockData = record
  { averageOperator = λ fine → fine
  ; averageAdjointOperator = λ coarse → coarse
  ; innerCoarseOperator = physicalTangentInner
  ; coarseZeroOperator = zeroPhysicalSU2Tangent4
  ; averageAdjointExact = λ fine coarse → refl
  ; innerCoarseZeroExact = scalarBondInnerZeroRight zeroPhysicalSU2Tangent4
  ; coarseNormNonnegativeExact = physicalTangentInnerNonnegative
  }

canonicalLiteralWilsonOperatorMatch :
  Path4SU2LiteralWilsonOperatorMatch PhysicalSU2Tangent4
canonicalLiteralWilsonOperatorMatch =
  literalWilsonOperatorMatch canonicalLiteralCoarseBlockData

open LiteralCoarseBlockData public

literalNonDivergenceHessianData : ∀ {Coarse} →
  LiteralCoarseBlockData Coarse → LiteralNonDivergenceHessianData Coarse
literalNonDivergenceHessianData coarseData = record
  { wilsonOperator = literalWilsonOperator
  ; averageOperator = averageOperator coarseData
  ; averageAdjointOperator = averageAdjointOperator coarseData
  ; innerCoarseOperator = innerCoarseOperator coarseData
  ; coarseZeroOperator = coarseZeroOperator coarseData
  ; averageAdjointExact = averageAdjointExact coarseData
  ; innerCoarseZeroExact = innerCoarseZeroExact coarseData
  ; coarseNormNonnegativeExact = coarseNormNonnegativeExact coarseData
  }

literalWilsonOperatorMatch : ∀ {Coarse} →
  LiteralCoarseBlockData Coarse → Path4SU2LiteralWilsonOperatorMatch Coarse
literalWilsonOperatorMatch coarseData = record
  { nonDivergenceData = literalNonDivergenceHessianData coarseData
  ; wilsonOperatorQuadraticMatchesLiteral = λ tangent →
      DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact.literalWilsonHessianEqualsCurlEnergy tangent
      |> λ wilson≡curl →
        DASHI.Physics.YangMills.BalabanPath4SU2LiteralWilsonOperatorRieszExact.physicalWilsonOperatorPairingExact tangent
      |> λ operator≡curl →
        Relation.Binary.PropositionalEquality.trans operator≡curl
          (Relation.Binary.PropositionalEquality.sym wilson≡curl)
  }
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  value |> function = function value

completeLiteralGaugeFixedHessianData : ∀ {Coarse} →
  LiteralCoarseBlockData Coarse →
  DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact.GaugeFixedHessianQuadraticData
    PhysicalSU2Tangent4
    DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.Lie3SiteField
    Coarse ℚ
completeLiteralGaugeFixedHessianData coarseData =
  literalGaugeFixedHessianQuadraticData
    (literalNonDivergenceHessianData coarseData)

completeLiteralGaugeFixedHessianPeriodicDecompositionExact :
  ∀ {Coarse} (coarseData : LiteralCoarseBlockData Coarse) tangent →
  DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact.gaugeFixedHessianQuadraticForm
    (completeLiteralGaugeFixedHessianData coarseData) tangent
  ≡ DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.physicalPeriodicReferenceDifferenceEnergy tangent
    Data.Rational._+_
    DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact.blockAverageNormSq
      (completeLiteralGaugeFixedHessianData coarseData) tangent
completeLiteralGaugeFixedHessianPeriodicDecompositionExact coarseData =
  literalConcreteDivergenceGaugeFixedDecompositionExact
    (literalWilsonOperatorMatch coarseData)

completeUniformReferenceHodgeCoercivity :
  ∀ {Coarse} (coarseData : LiteralCoarseBlockData Coarse) tangent →
  PhysicalBlockAverageZero tangent →
  DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate.configuredPathCoercivityConstant
    Data.Rational._*_
    physicalUnweightedNormSq tangent
  ≤ DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact.gaugeFixedHessianQuadraticForm
      (completeLiteralGaugeFixedHessianData coarseData) tangent
completeUniformReferenceHodgeCoercivity coarseData =
  uniformReferenceHodgeCoercivityFromConcreteDivergence
    (literalWilsonOperatorMatch coarseData)

completeLiteralWilsonOperatorRepresentativeLevel : ProofLevel
completeLiteralWilsonOperatorRepresentativeLevel = machineChecked

completeLiteralGaugeFixedHessianLevel : ProofLevel
completeLiteralGaugeFixedHessianLevel = machineChecked

completeUniformReferenceHodgeCoercivityLevel : ProofLevel
completeUniformReferenceHodgeCoercivityLevel = machineChecked
