module DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
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
