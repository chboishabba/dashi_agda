module DASHI.Physics.YangMills.BalabanPath4SU2LiteralDivergenceHessianInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  (literalWilsonHessianEqualsCurlEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralWilsonOperatorRieszExact using
  (literalWilsonOperator; physicalWilsonOperatorPairingExact)
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralGaugeFixedHessianAdapterExact using
  (Path4SU2LiteralWilsonOperatorMatch)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (squareNonnegative)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact using
  (Lie3; lie3; x; y; z; normSqV)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact using
  (siteSum4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using
    ( ScalarBondField4
    ; scalarBondInner
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using
    ( Lie3SiteField
    ; componentScalarBondField
    ; literalPeriodicDivergence
    ; literalNegativeForwardGradient
    ; physicalTangentInner
    ; gaugeLie3Inner
    ; literalGaugeFixingEnergy
    ; periodicDivergenceGradientAdjointSU2
    )

------------------------------------------------------------------------
-- Concrete additive structure on the physical tangent.
------------------------------------------------------------------------

addPhysicalTangent :
  PhysicalSU2Tangent4 → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
addPhysicalTangent left right component bond =
  left component bond + right component bond

addScalarBondField : ScalarBondField4 → ScalarBondField4 → ScalarBondField4
addScalarBondField left right axis site = left axis site + right axis site

siteInnerAddRight : ∀ left right first →
  siteSum4 (λ site → first site * (left site + right site))
  ≡ siteSum4 (λ site → first site * left site)
    + siteSum4 (λ site → first site * right site)
siteInnerAddRight left right first =
  trans
    (sumRationalCong (physicalBlockSites side4) _ _
      (λ site → ℚRing.solve-∀))
    (sumRationalAdd (physicalBlockSites side4)
      (λ site → first site * left site)
      (λ site → first site * right site))

scalarBondInnerAddRight : ∀ first left right →
  scalarBondInner first (addScalarBondField left right)
  ≡ scalarBondInner first left + scalarBondInner first right
scalarBondInnerAddRight first left right =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → siteInnerAddRight
        (left axis) (right axis) (first axis)))
    (sumRationalAdd (allCyclicIndices four)
      (λ axis → siteSum4 (λ site → first axis site * left axis site))
      (λ axis → siteSum4 (λ site → first axis site * right axis site)))

physicalTangentInnerAddRight : ∀ first left right →
  physicalTangentInner first (addPhysicalTangent left right)
  ≡ physicalTangentInner first left + physicalTangentInner first right
physicalTangentInnerAddRight first left right
  rewrite scalarBondInnerAddRight
    (componentScalarBondField first component1)
    (componentScalarBondField left component1)
    (componentScalarBondField right component1)
        | scalarBondInnerAddRight
    (componentScalarBondField first component2)
    (componentScalarBondField left component2)
    (componentScalarBondField right component2)
        | scalarBondInnerAddRight
    (componentScalarBondField first component3)
    (componentScalarBondField left component3)
    (componentScalarBondField right component3) =
  ℚRing.solve-∀

------------------------------------------------------------------------
-- Literal gauge inner-product positivity and zero laws.
------------------------------------------------------------------------

zeroLie3 : Lie3
zeroLie3 = lie3 0ℚ 0ℚ 0ℚ

zeroGaugeField : Lie3SiteField
zeroGaugeField site = zeroLie3

sumRationalZero : ∀ {A : Set} (values : List A) →
  sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumRationalZero [] = refl
sumRationalZero (value ∷ values)
  rewrite sumRationalZero values = ℚRing.solve-∀

zeroGaugeInnerZero : gaugeLie3Inner zeroGaugeField zeroGaugeField ≡ 0ℚ
zeroGaugeInnerZero =
  trans
    (sumRationalCong (physicalBlockSites side4) _ _
      (λ site → ℚRing.solve-∀))
    (sumRationalZero (physicalBlockSites side4))

lie3NormSqNonnegative : ∀ value → 0ℚ ≤ normSqV value
lie3NormSqNonnegative (lie3 a b c) =
  subst
    (λ left → left ≤ a * a + (b * b + c * c))
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (squareNonnegative a)
      (ℚP.+-mono-≤ (squareNonnegative b) (squareNonnegative c)))

gaugeLie3InnerNonnegative : ∀ gauge →
  0ℚ ≤ gaugeLie3Inner gauge gauge
gaugeLie3InnerNonnegative gauge = go (physicalBlockSites side4)
  where
  go : ∀ values → 0ℚ ≤ sumRational values (λ site → normSqV (gauge site))
  go [] = ℚP.≤-refl
  go (site ∷ sites) =
    subst
      (λ left → left ≤ normSqV (gauge site)
        + sumRational sites (λ current → normSqV (gauge current)))
      (ℚP.+-identityˡ 0ℚ)
      (ℚP.+-mono-≤ (lie3NormSqNonnegative (gauge site)) (go sites))

------------------------------------------------------------------------
-- Only the Wilson and coarse/block pieces remain supplied by the surrounding
-- configured Hessian.  The divergence, its adjoint, addition, and gauge norm
-- are concrete definitions here.
------------------------------------------------------------------------

record LiteralNonDivergenceHessianData (Coarse : Set) : Set₁ where
  field
    wilsonOperator : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
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

open LiteralNonDivergenceHessianData public

literalGaugeFixedHessianData : ∀ {Coarse} →
  LiteralNonDivergenceHessianData Coarse →
  GaugeFixedHessianData PhysicalSU2Tangent4 Lie3SiteField Coarse
literalGaugeFixedHessianData dataSet = record
  { wilsonHessian = wilsonOperator dataSet
  ; divergence = literalPeriodicDivergence
  ; divergenceStar = literalNegativeForwardGradient
  ; average = averageOperator dataSet
  ; averageStar = averageAdjointOperator dataSet
  ; addFine = addPhysicalTangent
  }

literalGaugeFixedHessianQuadraticData : ∀ {Coarse} →
  LiteralNonDivergenceHessianData Coarse →
  GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Lie3SiteField Coarse ℚ
literalGaugeFixedHessianQuadraticData dataSet = record
  { hessianData = literalGaugeFixedHessianData dataSet
  ; innerFine = physicalTangentInner
  ; innerGauge = gaugeLie3Inner
  ; innerCoarse = innerCoarseOperator dataSet
  ; addScalar = _+_
  ; scalarZero = 0ℚ
  ; gaugeZero = zeroGaugeField
  ; coarseZero = coarseZeroOperator dataSet
  ; innerFineAddRight = physicalTangentInnerAddRight
  ; divergenceAdjoint = periodicDivergenceGradientAdjointSU2
  ; averageAdjoint = averageAdjointExact dataSet
  ; innerGaugeZero = zeroGaugeInnerZero
  ; innerCoarseZero = innerCoarseZeroExact dataSet
  ; Nonnegative = λ value → 0ℚ ≤ value
  ; gaugeNormNonnegative = gaugeLie3InnerNonnegative
  ; coarseNormNonnegative = coarseNormNonnegativeExact dataSet
  }

literalConfiguredDivergenceIsStoredDivergence :
  ∀ {Coarse} (dataSet : LiteralNonDivergenceHessianData Coarse) tangent →
  divergence (literalGaugeFixedHessianData dataSet) tangent
  ≡ literalPeriodicDivergence tangent
literalConfiguredDivergenceIsStoredDivergence dataSet tangent = refl

literalConfiguredDivergenceStarIsNegativeForwardGradient :
  ∀ {Coarse} (dataSet : LiteralNonDivergenceHessianData Coarse) gauge →
  divergenceStar (literalGaugeFixedHessianData dataSet) gauge
  ≡ literalNegativeForwardGradient gauge
literalConfiguredDivergenceStarIsNegativeForwardGradient dataSet gauge = refl

literalGaugeFixingNormSqExact :
  ∀ {Coarse} (dataSet : LiteralNonDivergenceHessianData Coarse) tangent →
  gaugeFixingNormSq (literalGaugeFixedHessianQuadraticData dataSet) tangent
  ≡ literalGaugeFixingEnergy tangent
literalGaugeFixingNormSqExact dataSet tangent = refl

literalGaugeFixingQuadraticFormEqualsDivergenceEnergy :
  ∀ {Coarse} (dataSet : LiteralNonDivergenceHessianData Coarse) tangent →
  gaugeFixingQuadraticForm (literalGaugeFixedHessianQuadraticData dataSet) tangent
  ≡ literalGaugeFixingEnergy tangent
literalGaugeFixingQuadraticFormEqualsDivergenceEnergy dataSet tangent =
  trans
    (physicalGaugeFixingQuadraticFormExact
      (literalGaugeFixedHessianQuadraticData dataSet) tangent)
    (literalGaugeFixingNormSqExact dataSet tangent)

literalWilsonOperatorMatchExact :
  ∀ {Coarse} (dataSet : LiteralNonDivergenceHessianData Coarse) →
  (wilsonOperator dataSet ≡ literalWilsonOperator) →
  Path4SU2LiteralWilsonOperatorMatch Coarse
literalWilsonOperatorMatchExact dataSet eq = record
  { nonDivergenceData = dataSet
  ; wilsonOperatorQuadraticMatchesLiteral = λ tangent →
      trans
        (cong (λ op → physicalTangentInner tangent (op tangent)) eq)
        (trans
          (physicalWilsonOperatorPairingExact tangent)
          (sym (literalWilsonHessianEqualsCurlEnergy tangent)))
  }

literalDivergenceHessianInstanceLevel : ProofLevel
literalDivergenceHessianInstanceLevel = machineChecked

literalStoredDivergenceIdentificationLevel : ProofLevel
literalStoredDivergenceIdentificationLevel = machineChecked

literalGaugeFixingNormSqExactLevel : ProofLevel
literalGaugeFixingNormSqExactLevel = machineChecked
