{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinMarkedRowInfluenceAdapterRound273Exact where

------------------------------------------------------------------------
-- ROUND273 / OPTIONAL SAME-OBJECT ROW PRODUCER FOR R271
--
-- R271's canonical payment inside the optional Row-C tactic asks only for the
-- direct typed-Hessian influence majorant and one weighted-row inequality.
-- The existing shared-marked Hessian theorem can produce that row inequality
-- from a stronger SAME-OBJECT row identity.  Therefore this identity is a
-- useful producer tactic, not a mandatory C4b residual.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as Row
import DASHI.Physics.YangMills.BalabanLangevinDirectInfluencePaymentRound271Exact as R271

record MarkedRowDirectInfluenceProducer
    (Scale Volume Root : Set) : Set₁ where
  field
    hessian : R271.LiteralCMP109ActionHessianCarrier
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root
    embedding : Embed.OrderedRationalRealRingEmbedding

    sites : List (Langevin.Site (R271.frame hessian))
    metric : Metric.NatMetricTriangle (Langevin.Site (R271.frame hessian))
    influence :
      Langevin.Site (R271.frame hessian) →
      Langevin.Site (R271.frame hessian) → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    actionHessianAbsBelowInfluence : ∀ x y →
      absℝ (R271.actionHessianEntry hessian x y)
      ≤ℝ Embed.embed embedding (influence x y)

    rowDepth : Langevin.Site (R271.frame hessian) → Nat
    weightedInfluenceRowIsMarkedHessianPartial : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

open MarkedRowDirectInfluenceProducer public

asMarkedRowIdentification :
  ∀ {Scale Volume Root}
    (producer : MarkedRowDirectInfluenceProducer Scale Volume Root) →
  Row.LiteralHessianGeneratorRowIdentification
    Scale Volume Root
    (Langevin.Site (R271.frame (hessian producer)))
asMarkedRowIdentification producer = record
  { Row.LiteralHessianGeneratorRowIdentification.shared = shared producer
  ; Row.LiteralHessianGeneratorRowIdentification.scale = scale producer
  ; Row.LiteralHessianGeneratorRowIdentification.volume = volume producer
  ; Row.LiteralHessianGeneratorRowIdentification.root = root producer
  ; Row.LiteralHessianGeneratorRowIdentification.sites = sites producer
  ; Row.LiteralHessianGeneratorRowIdentification.metric = metric producer
  ; Row.LiteralHessianGeneratorRowIdentification.influence = influence producer
  ; Row.LiteralHessianGeneratorRowIdentification.influenceNonnegative =
      influenceNonnegative producer
  ; Row.LiteralHessianGeneratorRowIdentification.rowDepth = rowDepth producer
  ; Row.LiteralHessianGeneratorRowIdentification.generatorRowIsMarkedHessianPartial =
      weightedInfluenceRowIsMarkedHessianPartial producer
  }

compileMarkedRowProducer :
  ∀ {Scale Volume Root} →
  MarkedRowDirectInfluenceProducer Scale Volume Root →
  R271.DirectTypedHessianInfluencePayment Scale Volume Root
compileMarkedRowProducer producer = record
  { R271.DirectTypedHessianInfluencePayment.hessian = hessian producer
  ; R271.DirectTypedHessianInfluencePayment.shared = shared producer
  ; R271.DirectTypedHessianInfluencePayment.scale = scale producer
  ; R271.DirectTypedHessianInfluencePayment.volume = volume producer
  ; R271.DirectTypedHessianInfluencePayment.root = root producer
  ; R271.DirectTypedHessianInfluencePayment.embedding = embedding producer
  ; R271.DirectTypedHessianInfluencePayment.sites = sites producer
  ; R271.DirectTypedHessianInfluencePayment.metric = metric producer
  ; R271.DirectTypedHessianInfluencePayment.influence = influence producer
  ; R271.DirectTypedHessianInfluencePayment.influenceNonnegative =
      influenceNonnegative producer
  ; R271.DirectTypedHessianInfluencePayment.actionHessianAbsBelowInfluence =
      actionHessianAbsBelowInfluence producer
  ; R271.DirectTypedHessianInfluencePayment.weightedInfluenceRowBelowSharedHessian =
      Row.weightedGeneratorRowBound (asMarkedRowIdentification producer)
  }

round273MarkedRowToDirectPaymentCompilerLevel : ProofLevel
round273MarkedRowToDirectPaymentCompilerLevel = machineChecked

-- The exact same-object row identity remains a source theorem if this producer
-- route is chosen.  It is not a mandatory C4b or Clay residual.
round273MarkedRowProducerLevel : ProofLevel
round273MarkedRowProducerLevel = conditional
