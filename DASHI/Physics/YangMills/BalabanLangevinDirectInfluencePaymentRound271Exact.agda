{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinDirectInfluencePaymentRound271Exact where

------------------------------------------------------------------------
-- ROUND271 / NS-R592 LESSON INSIDE THE OPTIONAL ROW-C TACTIC
--
-- R270 correctly demotes the whole Heat/Doob -> Langevin -> Dyson route below
-- the canonical Clay mass-gap/clustering consumer.  If we nevertheless pursue
-- this useful tactic, C4b itself should still be least-privilege.
--
-- The spatial consumer does NOT require:
--   * the full differentiated Langevin commutator decomposition;
--   * the onsite connection term;
--   * R260's comparison + reference-anchor decomposition;
--   * a separately proved family of all Dyson-power estimates.
--
-- It requires only the SAME literal CMP109 action Hessian, a nonnegative
-- rational influence majorizing its absolute entries, and ONE weighted row
-- bound.  All weighted Dyson rows are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109LangevinTypedSecondVariationRound267Exact as R267
import DASHI.Physics.YangMills.BalabanLangevinAnchoredInfluenceRound268Exact as R268
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as WeightedBridge
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

------------------------------------------------------------------------
-- Minimal SAME-CMP109 C4b Hessian carrier.
------------------------------------------------------------------------

record LiteralCMP109ActionHessianCarrier : Set₁ where
  field
    carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier
    frame : Langevin.CompactLieLangevinFrameData
    background : Source.Background (Carrier.source carrier)
    siteTangent :
      Langevin.Site frame → Source.Tangent (Carrier.source carrier)

    actionHessianEntry :
      Langevin.Site frame → Langevin.Site frame → ℝ

    actionHessianIsCMP109Polarization : ∀ x y →
      actionHessianEntry x y
      ≡ Carrier.cmp109Polarization carrier background
          (siteTangent x) (siteTangent y)

open LiteralCMP109ActionHessianCarrier public

fromR267 :
  R267.LiteralCMP109LangevinSecondVariationWeld →
  LiteralCMP109ActionHessianCarrier
fromR267 dataSet = record
  { carrier = R267.carrier dataSet
  ; frame = R267.frame dataSet
  ; background = R267.background dataSet
  ; siteTangent = R267.siteTangent dataSet
  ; actionHessianEntry =
      Langevin.actionHessianEntry (R267.asTypedLangevinCommutator dataSet)
  ; actionHessianIsCMP109Polarization =
      R267.typedActionHessianIsCMP109Polarization dataSet
  }

------------------------------------------------------------------------
-- Canonical C4b payment inside the optional Row-C tactic.
------------------------------------------------------------------------

record DirectTypedHessianInfluencePayment
    (Scale Volume Root : Set) : Set₁ where
  field
    hessian : LiteralCMP109ActionHessianCarrier
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    embedding : Embed.OrderedRationalRealRingEmbedding
    sites : List (Langevin.Site (frame hessian))
    metric : Metric.NatMetricTriangle (Langevin.Site (frame hessian))

    influence :
      Langevin.Site (frame hessian) →
      Langevin.Site (frame hessian) → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    actionHessianAbsBelowInfluence : ∀ x y →
      absℝ (actionHessianEntry hessian x y)
      ≤ℝ Embed.embed embedding (influence x y)

    weightedInfluenceRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≤ Shared.hessianAnalyticConstant shared

open DirectTypedHessianInfluencePayment public

asMetricInfluenceBridge :
  ∀ {Scale Volume Root}
    (dataSet : DirectTypedHessianInfluencePayment Scale Volume Root) →
  Influence.SharedMarkedMetricInfluenceBridge
    Scale Volume Root
    (Langevin.Site (frame (hessian dataSet)))
asMetricInfluenceBridge dataSet = record
  { Influence.SharedMarkedMetricInfluenceBridge.shared = shared dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.scale = scale dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.volume = volume dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.root = root dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.sites = sites dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.metric = metric dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influence = influence dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influenceNonnegative =
      influenceNonnegative dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.weightedGeneratorRowBelowSharedHessian =
      weightedInfluenceRowBelowSharedHessian dataSet
  }

allWeightedDysonRows :
  ∀ {Scale Volume Root}
    (dataSet : DirectTypedHessianInfluencePayment Scale Volume Root)
    n x →
  Weighted.weightedPowerRow
    (WeightedBridge.asWeightedFiniteInfluence
      (Influence.asWeightedBridge (asMetricInfluenceBridge dataSet)))
    n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet))
      (Agda.Builtin.Nat.suc n)
allWeightedDysonRows dataSet =
  Influence.metricWeightedPowerRowBound (asMetricInfluenceBridge dataSet)

------------------------------------------------------------------------
-- Existing anchored R260/R268 construction is an ADAPTER, not a prerequisite.
------------------------------------------------------------------------

fromR268 :
  ∀ {Scale Volume Root} →
  R268.LiteralAnchoredLangevinInfluence Scale Volume Root →
  DirectTypedHessianInfluencePayment Scale Volume Root
fromR268 dataSet = record
  { hessian = fromR267 (R268.cmpLangevin dataSet)
  ; shared = R268.shared dataSet
  ; scale = R268.scale dataSet
  ; volume = R268.volume dataSet
  ; root = R268.root dataSet
  ; embedding = R268.embedding dataSet
  ; sites = R268.sites dataSet
  ; metric = R268.metric dataSet
  ; influence = R268.anchoredInfluence dataSet
  ; influenceNonnegative = R268.anchoredInfluenceNonnegative dataSet
  ; actionHessianAbsBelowInfluence =
      R268.typedActionHessianAbsBelowAnchoredInfluence dataSet
  ; weightedInfluenceRowBelowSharedHessian =
      R268.weightedAnchoredDebtBelowSharedHessian dataSet
  }

round271DirectInfluenceCompilerLevel : ProofLevel
round271DirectInfluenceCompilerLevel = machineChecked

round271R268AdapterLevel : ProofLevel
round271R268AdapterLevel = machineChecked

-- Actual source-level inhabitant of the direct payment remains open.
round271DirectTypedHessianInfluencePaymentLevel : ProofLevel
round271DirectTypedHessianInfluencePaymentLevel = conditional

record Round271Boundary : Set where
  constructor round271-boundary
  field
    fullTypedCommutatorMandatoryForC4b : Bool
    fullTypedCommutatorMandatoryForC4bIsFalse :
      fullTypedCommutatorMandatoryForC4b ≡ false

    anchoredComparisonReferenceDecompositionMandatoryForC4b : Bool
    anchoredComparisonReferenceDecompositionMandatoryForC4bIsFalse :
      anchoredComparisonReferenceDecompositionMandatoryForC4b ≡ false

    allDysonRowsPrimitivePhysicalDebt : Bool
    allDysonRowsPrimitivePhysicalDebtIsFalse :
      allDysonRowsPrimitivePhysicalDebt ≡ false

    directSameCMP109HessianInfluencePaymentIsPreferredTacticLeaf : Bool
    directSameCMP109HessianInfluencePaymentIsPreferredTacticLeafIsTrue :
      directSameCMP109HessianInfluencePaymentIsPreferredTacticLeaf ≡ true

    rowCTacticMandatoryForClayMassGap : Bool
    rowCTacticMandatoryForClayMassGapIsFalse :
      rowCTacticMandatoryForClayMassGap ≡ false

canonicalRound271Boundary : Round271Boundary
canonicalRound271Boundary =
  round271-boundary false refl false refl false refl true refl false refl
