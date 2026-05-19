module DASHI.Physics.Toy.RGSummaryBundle where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Physics.PhysicalTheory as PT
import DASHI.Physics.Measurement as Meas
import DASHI.Physics.Benchmark as Bench
open import DASHI.Physics.Toy.RGUniversality as RG

record RGAsymptoticBundle (n : Nat) (x : RG.RGState n) : Set where
  field
    basin-stable :
      ∀ k → RG.rgBasinLabel (RG.stepPow n k x) ≡ RG.rgBasinLabel x
    irrelevant-step-monotone :
      ∀ k →
      RG.rgIrrelevantSize (RG.stepPow n (suc k) x) ≤
      RG.rgIrrelevantSize (RG.stepPow n k x)
    irrelevant-bounded :
      ∀ k →
      RG.rgIrrelevantSize (RG.stepPow n k x) ≤
      RG.rgIrrelevantSize x
    relevant-observable-stable :
      ∀ k →
      RG.rgObservableExprEval n RG.rel# (RG.rgClassOf (RG.stepPow n k x)) ≡
      RG.rgObservableExprEval n RG.rel# (RG.rgClassOf x)
    irrelevant-observable-step-monotone :
      ∀ k →
      RG.rgObservableExprEval n RG.irr# (RG.rgClassOf (RG.stepPow n (suc k) x)) ≤
      RG.rgObservableExprEval n RG.irr# (RG.rgClassOf (RG.stepPow n k x))

rgAsymptoticBundle : ∀ n (x : RG.RGState n) → RGAsymptoticBundle n x
rgAsymptoticBundle n x =
  let witness = RG.rgAsymptoticWitness n x in
  record
    { basin-stable = proj₁ witness
    ; irrelevant-step-monotone = proj₁ (proj₂ witness)
    ; irrelevant-bounded = proj₁ (proj₂ (proj₂ witness))
    ; relevant-observable-stable = proj₁ (proj₂ (proj₂ (proj₂ witness)))
    ; irrelevant-observable-step-monotone = proj₂ (proj₂ (proj₂ (proj₂ witness)))
    }

record RGRecoveredTailBundle (n k : Nat) (x : RG.RGState n) : Set where
  field
    canonical-class :
      ∀ m →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.stepPow n k x) →
      RG.rgClassOf (RG.stepPow n m (RG.stepPow n k x)) ≡
      RG.rgCanonicalClass n (RG.relevantMode x)
    observable-collapse :
      ∀ m O →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.stepPow n k x) →
      RG.rgObservableExprEval n O (RG.rgClassOf (RG.stepPow n m (RG.stepPow n k x))) ≡
      RG.rgObservableExprEval n O (RG.rgCanonicalClass n (RG.relevantMode x))

rgRecoveredTailBundle :
  ∀ n k (x : RG.RGState n) → RGRecoveredTailBundle n k x
rgRecoveredTailBundle n k x =
  record
    { canonical-class = λ m rx → RG.rgRecovered-stepPow-tail-canonical n k m x rx
    ; observable-collapse = λ m O rx → RG.rgRecovered-stepPow-tail-canonical-observable n k m O x rx
    }

record RGRenormalizationSummary : Set₁ where
  field
    bundle : RG.RGRenormalizationBundle

rgRenormalizationSummary : RGRenormalizationSummary
rgRenormalizationSummary =
  record
    { bundle = RG.rgRenormalizationBundle
    }

record RGFlowSummary : Set₁ where
  field
    bundle : RG.RGFlowBundle

rgFlowSummary : RGFlowSummary
rgFlowSummary =
  record
    { bundle = RG.rgFlowBundle
    }

record RGFusedSummary : Set₁ where
  field
    bundle : RG.RGFusedBundle

rgFusedSummary : RGFusedSummary
rgFusedSummary =
  record
    { bundle = RG.rgFusedBundle
    }

record RGPhase2HierarchySummary : Set₁ where
  field
    bundle : RG.RGPhase2HierarchyBundle

rgPhase2HierarchySummary : RGPhase2HierarchySummary
rgPhase2HierarchySummary =
  record
    { bundle = RG.rgPhase2HierarchyBundle
    }

record RGPredictionSummary (n : Nat) : Set₁ where
  field
    theory : Meas.PredictionTheory (RG.rgQuotiented n)

rgPredictionSummary : (n : Nat) → RGPredictionSummary n
rgPredictionSummary n =
  record
    { theory = RG.rgPredictionTheory n
    }

record RGScheduledPredictionSummary (n : Nat) : Set₁ where
  field
    theory : Meas.PredictionTheory (RG.rgRawQuotiented n)

rgScheduledPredictionSummary : (n : Nat) → RGScheduledPredictionSummary n
rgScheduledPredictionSummary n =
  record
    { theory = RG.rgScheduledPredictionTheory n
    }

record RGBenchmarkSummary (n : Nat) : Set₁ where
  field
    theory : Bench.BenchmarkTheory′ (RG.rgQuotiented n)
    match  : Bench.BenchmarkMatch theory

rgBenchmarkSummary : (n : Nat) → RGBenchmarkSummary n
rgBenchmarkSummary n =
  record
    { theory = RG.rgBenchmarkTheory n
    ; match = RG.rgBenchmarkMatch n
    }

record RGRichBenchmarkSummary (n : Nat) : Set₁ where
  field
    theory : Bench.BenchmarkTheory′ (RG.rgQuotiented n)
    match  : Bench.BenchmarkMatch theory
    self-mismatch-zero :
      ∀ gain (st : RG.RGPhysState n) →
      Bench.BenchmarkMatch.mismatch (RG.rgRichBenchmarkMatch n) gain st (RG.rgBenchmarkDataset n gain st) ≡
      RG.zeroRGBenchmarkScore

rgRichBenchmarkSummary : (n : Nat) → RGRichBenchmarkSummary n
rgRichBenchmarkSummary n =
  record
    { theory = RG.rgBenchmarkTheory n
    ; match = RG.rgRichBenchmarkMatch n
    ; self-mismatch-zero = RG.rgRichBenchmarkSelfMismatch-zero n
    }

record RGScheduledBenchmarkSummary (n : Nat) : Set₁ where
  field
    theory : Bench.BenchmarkTheory′ (RG.rgRawQuotiented n)
    rel-stable :
      ∀ gain t (x : RG.RGState n) →
      Bench.BenchmarkTheory′.predictB (RG.rgScheduledBenchmarkTheory n) (gain , t) RG.rel# x ≡
      gain * RG.rgObservableExprEval n RG.rel# (RG.rgClassOf x)
    irr-step-monotone :
      ∀ gain t (x : RG.RGState n) →
      Bench.BenchmarkTheory′.predictB (RG.rgScheduledBenchmarkTheory n) (gain , suc t) RG.irr# x ≤
      Bench.BenchmarkTheory′.predictB (RG.rgScheduledBenchmarkTheory n) (gain , t) RG.irr# x

rgScheduledBenchmarkSummary : (n : Nat) → RGScheduledBenchmarkSummary n
rgScheduledBenchmarkSummary n =
  record
    { theory = RG.rgScheduledBenchmarkTheory n
    ; rel-stable = RG.rgScheduled-rel-benchmark-stable n
    ; irr-step-monotone = RG.rgScheduled-irr-benchmark-step-monotone n
    }

record RGMixedScheduledBenchmarkSummary (n k : Nat) : Set₁ where
  field
    theory : RG.RGMixedSchedule n k → Bench.BenchmarkTheory′ (RG.rgRawQuotiented (k + n))
    rich-match : (sch : RG.RGMixedSchedule n k) → Bench.BenchmarkMatch (RG.rgMixedBenchmarkTheory n sch)
    self-mismatch-zero :
      ∀ (sch : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixedBenchmarkMatch n sch)
        gain
        x
        (RG.rgMixedBenchmarkDataset n sch gain x)
      ≡ zero
    rich-self-mismatch-zero :
      ∀ (sch : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixedRichBenchmarkMatch n sch)
        gain
        x
        (RG.rgMixedBenchmarkDataset n sch gain x)
      ≡ RG.zeroRGBenchmarkScore
    rel-stable :
      ∀ (sch : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgMixedBenchmarkTheory n sch) gain RG.rel# x ≡
      gain * RG.rgObservableExprEval (k + n) RG.rel# (RG.rgClassOf x)
    irr-bounded :
      ∀ (sch : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgMixedBenchmarkTheory n sch) gain RG.irr# x ≤
      gain * RG.rgIrrelevantSize x
    uniform-one-agree :
      ∀ gain (O : RG.RGObservableExpr) (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB
        (RG.rgMixedBenchmarkTheory n (RG.uniformMixed n k (suc zero)))
        gain O x
      ≡
      Bench.BenchmarkTheory′.predictB
        (RG.rgBenchmarkTheory n)
        gain O (RG.rgClassOf (RG.rgFused k n x))
    rel-agree :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgMixedBenchmarkTheory n sch₁) gain RG.rel# x ≡
      Bench.BenchmarkTheory′.predictB (RG.rgMixedBenchmarkTheory n sch₂) gain RG.rel# x
    recovered-same-class :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₂ x) →
      RG.rgClassOf (RG.rgRunMixed sch₁ x) ≡ RG.rgClassOf (RG.rgRunMixed sch₂ x)
    recovered-mismatch-zero :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₂ x) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixedBenchmarkMatch n sch₁)
        gain
        x
        (RG.rgMixedBenchmarkDataset n sch₂ gain x)
      ≡ zero
    recovered-rich-mismatch-zero :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₂ x) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixedRichBenchmarkMatch n sch₁)
        gain
        x
        (RG.rgMixedBenchmarkDataset n sch₂ gain x)
      ≡ RG.zeroRGBenchmarkScore
    step-tail-canonical :
      ∀ (sch : RG.RGMixedSchedule n k) t (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch x) →
      RG.rgClassOf (RG.stepPow n t (RG.rgRunMixed sch x)) ≡
      RG.rgClassOf (RG.rgVacuum n (RG.rgBasinLabel x))
    step-tail-canonical-observable :
      ∀ (sch : RG.RGMixedSchedule n k) t (O : RG.RGObservableExpr) (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch x) →
      RG.rgObservableExprEval n O (RG.rgClassOf (RG.stepPow n t (RG.rgRunMixed sch x))) ≡
      RG.rgObservableExprEval n O (RG.rgClassOf (RG.rgVacuum n (RG.rgBasinLabel x)))
    step-tail-benchmark-mismatch-zero :
      ∀ (sch : RG.RGMixedSchedule n k) t gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch x) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgBenchmarkMatch n)
        gain
        (RG.rgClassOf (RG.stepPow n t (RG.rgRunMixed sch x)))
        (RG.rgBenchmarkDataset n gain (RG.rgClassOf (RG.rgVacuum n (RG.rgBasinLabel x))))
      ≡ zero
    step-tail-cross-benchmark-mismatch-zero :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) t gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₂ x) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgBenchmarkMatch n)
        gain
        (RG.rgClassOf (RG.stepPow n t (RG.rgRunMixed sch₁ x)))
        (RG.rgBenchmarkDataset n gain (RG.rgClassOf (RG.stepPow n t (RG.rgRunMixed sch₂ x))))
      ≡ zero

record RGMixedTraceBenchmarkSummary (n k : Nat) : Set₁ where
  field
    theory : RG.RGMixedSchedule n k → Bench.BenchmarkTheory′ (RG.rgRawQuotiented (k + n))
    match : (sch : RG.RGMixedSchedule n k) → Bench.BenchmarkMatch (RG.rgMixedTraceBenchmarkTheory n sch)
    self-mismatch-zero :
      ∀ (sch : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixedTraceBenchmarkMatch n sch)
        gain
        x
        (RG.rgMixedTraceBenchmarkDataset n sch gain x)
      ≡ RG.zeroRGBenchmarkScore
    recovered-endpoint-zero :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule n k) gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed sch₂ x) →
      RG.RGBenchmarkScore.endpoint
        (Bench.BenchmarkMatch.mismatch
          (RG.rgMixedTraceBenchmarkMatch n sch₁)
          gain
          x
          (RG.rgMixedTraceBenchmarkDataset n sch₂ gain x))
      ≡ zero

record RGMixedPhase2TraceBenchmarkSummary (n k : Nat) : Set₁ where
  field
    theory : RG.RGMixedSchedule2 n k → Bench.BenchmarkTheory′ (RG.rgRawQuotiented (k + n))
    match : (sch : RG.RGMixedSchedule2 n k) → Bench.BenchmarkMatch (RG.rgMixed2TraceBenchmarkTheory n sch)
    self-mismatch-zero :
      ∀ (sch : RG.RGMixedSchedule2 n k) gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgMixed2TraceBenchmarkMatch n sch)
        gain
        x
        (RG.rgMixed2TraceBenchmarkDataset n sch gain x)
      ≡ RG.zeroRGBenchmarkScore
    recovered-endpoint-zero :
      ∀ (sch₁ sch₂ : RG.RGMixedSchedule2 n k) gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed2 sch₁ x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgRunMixed2 sch₂ x) →
      RG.RGBenchmarkScore.endpoint
        (Bench.BenchmarkMatch.mismatch
          (RG.rgMixed2TraceBenchmarkMatch n sch₁)
          gain
          x
          (RG.rgMixed2TraceBenchmarkDataset n sch₂ gain x))
      ≡ zero
    tail-vs-flip-vacuum-split :
      ∀ r →
      RG.rgClassOf (RG.rgRunMixed2 (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc zero) zero) (RG.rgVacuum (suc n) r)) ≡
      RG.rgClassOf (RG.rgRunMixed2 (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc zero) zero) (RG.rgVacuum (suc n) r))
      ×
      RG.RGBenchmarkScore.path
        (Bench.BenchmarkMatch.mismatch
          (RG.rgMixed2TraceBenchmarkMatch n (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc zero) zero))
          (suc zero)
          (RG.rgVacuum (suc n) r)
          (RG.rgMixed2TraceBenchmarkDataset n (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc zero) zero) (suc zero) (RG.rgVacuum (suc n) r)))
      ≡ suc zero
    uniform-tail-vs-flip-positive-depth-split :
      ∀ k r →
      RG.RGBenchmarkScore.endpoint
        (Bench.BenchmarkMatch.mismatch
          (RG.rgMixed2TraceBenchmarkMatch n (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc k) zero))
          (suc zero)
          (RG.rgVacuum ((suc k) + n) r)
          (RG.rgMixed2TraceBenchmarkDataset n (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc k) zero) (suc zero) (RG.rgVacuum ((suc k) + n) r)))
      ≡ zero
      ×
      RG.RGBenchmarkScore.path
        (Bench.BenchmarkMatch.mismatch
          (RG.rgMixed2TraceBenchmarkMatch n (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc k) zero))
          (suc zero)
          (RG.rgVacuum ((suc k) + n) r)
          (RG.rgMixed2TraceBenchmarkDataset n (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc k) zero) (suc zero) (RG.rgVacuum ((suc k) + n) r)))
      ≡ suc zero
    one-layer-hold-raw-split :
      ∀ (x : RG.RGState (suc n)) →
      RG.rgClassOf (RG.rgRunMixed2 (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc zero) zero) x) ≡
      RG.rgClassOf (RG.rgRunMixed2 (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc zero) zero) x)
      ×
      suc (RG.rgMixed2TraceObservableEval n (RG.uniformMixed2 RG.tailScheme RG.holdMode n (suc zero) zero) RG.path2RG x) ≡
      RG.rgMixed2TraceObservableEval n (RG.uniformMixed2 RG.flipTailScheme RG.holdMode n (suc zero) zero) RG.path2RG x

rgMixedScheduledBenchmarkSummary : (n k : Nat) → RGMixedScheduledBenchmarkSummary n k
rgMixedScheduledBenchmarkSummary n k =
  record
    { theory = RG.rgMixedBenchmarkTheory n
    ; rich-match = RG.rgMixedRichBenchmarkMatch n
    ; self-mismatch-zero = RG.rgMixedBenchmarkSelfMismatch-zero n
    ; rich-self-mismatch-zero = RG.rgMixedRichBenchmarkSelfMismatch-zero n
    ; rel-stable = RG.rgMixed-rel-benchmark-stable n
    ; irr-bounded = RG.rgMixed-irr-benchmark-bounded n
    ; uniform-one-agree = RG.rgUniformMixed-one-benchmark-agree k n
    ; rel-agree = λ sch₁ sch₂ gain x → RG.rgMixed-rel-benchmark-agree n sch₁ sch₂ gain RG.rel# x refl
    ; recovered-same-class = RG.rgMixed-recovered-same-class n
    ; recovered-mismatch-zero = RG.rgMixed-recovered-benchmark-mismatch-zero n
    ; recovered-rich-mismatch-zero = RG.rgMixed-recovered-rich-benchmark-mismatch-zero n
    ; step-tail-canonical = RG.rgMixed-step-tail-canonical n
    ; step-tail-canonical-observable = RG.rgMixed-step-tail-canonical-observable n
    ; step-tail-benchmark-mismatch-zero = RG.rgMixed-step-tail-benchmark-mismatch-zero n
    ; step-tail-cross-benchmark-mismatch-zero = RG.rgMixed-step-tail-cross-benchmark-mismatch-zero n
    }

rgMixedTraceBenchmarkSummary : (n k : Nat) → RGMixedTraceBenchmarkSummary n k
rgMixedTraceBenchmarkSummary n k =
  record
    { theory = RG.rgMixedTraceBenchmarkTheory n
    ; match = RG.rgMixedTraceBenchmarkMatch n
    ; self-mismatch-zero = RG.rgMixedTraceBenchmarkSelfMismatch-zero n
    ; recovered-endpoint-zero = RG.rgMixedTraceRecovered-endpoint-zero n
    }

rgMixedPhase2TraceBenchmarkSummary : (n k : Nat) → RGMixedPhase2TraceBenchmarkSummary n k
rgMixedPhase2TraceBenchmarkSummary n k =
  record
    { theory = RG.rgMixed2TraceBenchmarkTheory n
    ; match = RG.rgMixed2TraceBenchmarkMatch n
    ; self-mismatch-zero = RG.rgMixed2TraceBenchmarkSelfMismatch-zero n
    ; recovered-endpoint-zero = RG.rgMixed2TraceRecovered-endpoint-zero n
    ; tail-vs-flip-vacuum-split = λ r →
        RG.rgMixed2-tail-vs-flip-endpoint-class-on-vacuum n r ,
        proj₂ (RG.rgMixed2-tail-vs-flip-trace-benchmark-split n r)
    ; uniform-tail-vs-flip-positive-depth-split = λ k r →
        RG.rgUniformMixed2-tail-vs-flip-trace-benchmark-split k n r
    ; one-layer-hold-raw-split = λ x →
        RG.rgMixed2-tail-vs-flip-one-layer-hold-endpoint-class n x ,
        RG.rgMixed2-tail-vs-flip-one-layer-hold-path-step n x
    }

record RGBenchmarkComparisonBundle (n : Nat) : Set₁ where
  field
    fused-flow-rel-agree :
      ∀ k m gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.rel#
        (RG.rgClassOf (RG.rgFused k n x))
      ≡
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.rel#
        (RG.rgClassOf (RG.rgFlow k m n x))
    fused-stepPow-flow-rel-agree :
      ∀ k t gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.rel#
        (RG.rgClassOf (RG.stepPow n t (RG.rgFused k n x)))
      ≡
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.rel#
        (RG.rgClassOf (RG.rgFlow k (suc t) n x))
    flow-irr-step-monotone :
      ∀ k m gain (x : RG.RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.irr#
        (RG.rgClassOf (RG.rgFlow k (suc m) n x))
      ≤
      Bench.BenchmarkTheory′.predictB (RG.rgBenchmarkTheory n) gain RG.irr#
        (RG.rgClassOf (RG.rgFlow k m n x))
    recovered-mismatch-zero :
      ∀ k m gain (x : RG.RGState (k + n)) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgFused k n x) →
      PT.recoveredLaw (RG.rgShellTheory n) (RG.rgFlow k m n x) →
      Bench.BenchmarkMatch.mismatch
        (RG.rgBenchmarkMatch n)
        gain
        (RG.rgClassOf (RG.rgFused k n x))
        (RG.rgBenchmarkDataset n gain (RG.rgClassOf (RG.rgFlow k m n x)))
      ≡ zero

rgBenchmarkComparisonBundle : (n : Nat) → RGBenchmarkComparisonBundle n
rgBenchmarkComparisonBundle n =
  record
    { fused-flow-rel-agree = λ k m gain x → RG.rgFused-flow-rel-benchmark-agree k m n gain x
    ; fused-stepPow-flow-rel-agree = λ k t gain x → RG.rgFused-stepPow-flow-rel-benchmark-agree k t n gain x
    ; flow-irr-step-monotone = λ k m gain x → RG.rgFlow-irr-benchmark-step-monotone k m n gain x
    ; recovered-mismatch-zero = λ k m gain x rxf rflow → RG.rgFused-flow-recovered-benchmark-mismatch-zero k m n gain x rxf rflow
    }
