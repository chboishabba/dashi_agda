module DASHI.Statistics.Vec15Inference where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Statistics.Vec15Descriptive using
  ( PrimeCarrier15
  ; sum15
  ; max15
  ; countNonZero15
  )

------------------------------------------------------------------------
-- Minimal concrete inference / modeling surface for the 15-prime carrier.
--
-- The deterministic core stays intentionally small:
--   - a boolean decision surface
--   - a simple confidence-interval scaffold
--   - baseline test results built from descriptive summaries
--
-- More ambitious operators are still present, but they now reuse the same
-- cheap concrete core rather than remaining pure placeholders.

data Decision : Set where
  reject : Decision
  failToReject : Decision

data HypothesisTag : Set where
  nullTag : HypothesisTag
  alternativeTag : HypothesisTag

record Hypothesis : Set where
  field
    null : HypothesisTag
    alternative : HypothesisTag

record ConfidenceInterval : Set where
  field
    lower : Nat
    upper : Nat

record TestResult : Set where
  field
    hypothesis : Hypothesis
    statistic : Nat
    pValue : Nat
    decision : Decision
    interval : ConfidenceInterval
    rejectBit : Bool
    failBit : Bool
    intervalConsistent : Bool

record CorrelationResult : Set where
  field
    coefficient : Nat
    test : TestResult

record RegressionResult : Set where
  field
    fitStatistic : Nat
    test : TestResult

record PCAResult : Set where
  field
    componentCount : Nat
    test : TestResult

record ClusterResult : Set where
  field
    clusterCount : Nat
    test : TestResult

record FactorAnalysisResult : Set where
  field
    factorCount : Nat
    test : TestResult

record ModelInput : Set where
  field
    values : PrimeCarrier15
    test : TestResult
    decisionBit : Bool
    failBit : Bool
    intervalConsistent : Bool
    support : Nat
    contrast : Nat

record PairwiseModelInput : Set where
  field
    left : PrimeCarrier15
    right : PrimeCarrier15
    test : TestResult
    decisionBit : Bool
    failBit : Bool
    intervalConsistent : Bool
    support : Nat
    contrast : Nat

------------------------------------------------------------------------
-- Cheap deterministic helpers.

leqNat : Nat → Nat → Bool
leqNat zero _ = true
leqNat (suc _) zero = false
leqNat (suc m) (suc n) = leqNat m n

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

decisionIsReject : Decision → Bool
decisionIsReject reject = true
decisionIsReject failToReject = false

decisionIsFail : Decision → Bool
decisionIsFail d = boolNot (decisionIsReject d)

testResultIsReject : TestResult → Bool
testResultIsReject r = TestResult.rejectBit r

testResultIsFail : TestResult → Bool
testResultIsFail r = TestResult.failBit r

confidenceInterval15 : Nat → PrimeCarrier15 → ConfidenceInterval
confidenceInterval15 level xs = record
  { lower = zero
  ; upper = max15 xs + level
  }

confidenceIntervalContains : Nat → ConfidenceInterval → Bool
confidenceIntervalContains x interval with leqNat (ConfidenceInterval.lower interval) x
... | true = leqNat x (ConfidenceInterval.upper interval)
... | false = false

confidenceIntervalValid : ConfidenceInterval → Bool
confidenceIntervalValid interval =
  leqNat (ConfidenceInterval.lower interval) (ConfidenceInterval.upper interval)

testResultWithinInterval : TestResult → Bool
testResultWithinInterval r =
  confidenceIntervalContains (TestResult.statistic r) (TestResult.interval r)

testResultIsWellFormed : TestResult → Bool
testResultIsWellFormed r = TestResult.intervalConsistent r

baselineDecision : PrimeCarrier15 → Decision
baselineDecision xs with leqNat (sum15 xs) (countNonZero15 xs)
... | true = failToReject
... | false = reject

baselineTestResult : Hypothesis → PrimeCarrier15 → TestResult
baselineTestResult h xs = let
  statistic = sum15 xs
  pValue = countNonZero15 xs
  interval = confidenceInterval15 zero xs
  decision = baselineDecision xs
  in record
  { hypothesis = h
  ; statistic = statistic
  ; pValue = pValue
  ; decision = decision
  ; interval = interval
  ; rejectBit = decisionIsReject decision
  ; failBit = decisionIsFail decision
  ; intervalConsistent =
      andBool
        (confidenceIntervalValid interval)
        (confidenceIntervalContains statistic interval)
  }

pairStatistic : PrimeCarrier15 → PrimeCarrier15 → Nat
pairStatistic xs ys = sum15 xs + sum15 ys

pairPValue : PrimeCarrier15 → PrimeCarrier15 → Nat
pairPValue xs ys = countNonZero15 xs + countNonZero15 ys

pairSupport : PrimeCarrier15 → PrimeCarrier15 → Nat
pairSupport xs ys = countNonZero15 xs + countNonZero15 ys

pairContrast : PrimeCarrier15 → PrimeCarrier15 → Nat
pairContrast xs ys = pairStatistic xs ys + pairSupport xs ys

pairDecision : PrimeCarrier15 → PrimeCarrier15 → Decision
pairDecision xs ys with leqNat (pairStatistic xs ys) (pairPValue xs ys)
... | true = failToReject
... | false = reject

pairInterval : PrimeCarrier15 → PrimeCarrier15 → ConfidenceInterval
pairInterval xs ys = record
  { lower = zero
  ; upper = pairStatistic xs ys + pairPValue xs ys
  }

pairTestResult : Hypothesis → PrimeCarrier15 → PrimeCarrier15 → TestResult
pairTestResult h xs ys = let
  statistic = pairStatistic xs ys
  pValue = pairPValue xs ys
  interval = pairInterval xs ys
  decision = pairDecision xs ys
  in record
  { hypothesis = h
  ; statistic = statistic
  ; pValue = pValue
  ; decision = decision
  ; interval = interval
  ; rejectBit = decisionIsReject decision
  ; failBit = decisionIsFail decision
  ; intervalConsistent =
      andBool
        (confidenceIntervalValid interval)
        (confidenceIntervalContains statistic interval)
  }

modelHypothesis : Hypothesis
modelHypothesis = record
  { null = nullTag
  ; alternative = alternativeTag
  }

------------------------------------------------------------------------
-- Named inferential and modeling operators.
--
-- These are still modest by design, but they are no longer empty shells:
-- they reuse the same deterministic baseline test semantics.

anova15 : PrimeCarrier15 → TestResult
anova15 = baselineTestResult modelHypothesis

chiSquared15 : PrimeCarrier15 → TestResult
chiSquared15 = baselineTestResult modelHypothesis

tTest15 : PrimeCarrier15 → PrimeCarrier15 → TestResult
tTest15 xs ys = pairTestResult modelHypothesis xs ys

mannWhitney15 : PrimeCarrier15 → PrimeCarrier15 → TestResult
mannWhitney15 xs ys = pairTestResult modelHypothesis xs ys

kruskalWallis15 : PrimeCarrier15 → TestResult
kruskalWallis15 = baselineTestResult modelHypothesis

pearsonCorrelation15 : PrimeCarrier15 → PrimeCarrier15 → CorrelationResult
pearsonCorrelation15 xs ys = record
  { coefficient = pairStatistic xs ys
  ; test = pairTestResult modelHypothesis xs ys
  }

spearmanCorrelation15 : PrimeCarrier15 → PrimeCarrier15 → CorrelationResult
spearmanCorrelation15 xs ys = record
  { coefficient = pairPValue xs ys
  ; test = pairTestResult modelHypothesis xs ys
  }

regression15 : PrimeCarrier15 → PrimeCarrier15 → RegressionResult
regression15 xs ys = record
  { fitStatistic = pairStatistic xs ys + pairPValue xs ys
  ; test = pairTestResult modelHypothesis xs ys
  }

factorAnalysis15 : PrimeCarrier15 → FactorAnalysisResult
factorAnalysis15 xs = record
  { factorCount = countNonZero15 xs
  ; test = baselineTestResult modelHypothesis xs
  }

pca15 : PrimeCarrier15 → PCAResult
pca15 xs = record
  { componentCount = countNonZero15 xs
  ; test = baselineTestResult modelHypothesis xs
  }

cluster15 : Nat → PrimeCarrier15 → ClusterResult
cluster15 k xs = record
  { clusterCount = k
  ; test = baselineTestResult modelHypothesis xs
  }

modelInput15 : PrimeCarrier15 → ModelInput
modelInput15 xs = let
  test = baselineTestResult modelHypothesis xs
  in record
    { values = xs
    ; test = test
    ; decisionBit = testResultIsReject test
    ; failBit = testResultIsFail test
    ; intervalConsistent = testResultIsWellFormed test
    ; support = countNonZero15 xs
    ; contrast = sum15 xs
    }

pairwiseModelInput15 : PrimeCarrier15 → PrimeCarrier15 → PairwiseModelInput
pairwiseModelInput15 xs ys = let
  test = pairTestResult modelHypothesis xs ys
  in record
    { left = xs
    ; right = ys
    ; test = test
    ; decisionBit = testResultIsReject test
    ; failBit = testResultIsFail test
    ; intervalConsistent = testResultIsWellFormed test
    ; support = pairSupport xs ys
    ; contrast = pairContrast xs ys
    }

------------------------------------------------------------------------
-- Package the surface in one record so downstream lanes can depend on a
-- single import without coupling to any one operator.

record InferenceSurface15 : Set₁ where
  field
    carrier : Set
    carrier15 : carrier
    anova : PrimeCarrier15 → TestResult
    chiSquared : PrimeCarrier15 → TestResult
    tTest : PrimeCarrier15 → PrimeCarrier15 → TestResult
    mannWhitney : PrimeCarrier15 → PrimeCarrier15 → TestResult
    kruskalWallis : PrimeCarrier15 → TestResult
    pearsonCorrelation : PrimeCarrier15 → PrimeCarrier15 → CorrelationResult
    spearmanCorrelation : PrimeCarrier15 → PrimeCarrier15 → CorrelationResult
    regression : PrimeCarrier15 → PrimeCarrier15 → RegressionResult
    factorAnalysis : PrimeCarrier15 → FactorAnalysisResult
    pca : PrimeCarrier15 → PCAResult
    cluster : Nat → PrimeCarrier15 → ClusterResult

open InferenceSurface15 public

inferenceSurface15 : InferenceSurface15
inferenceSurface15 = record
  { carrier = PrimeCarrier15
  ; carrier15 = mkVec15 zero zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  ; anova = anova15
  ; chiSquared = chiSquared15
  ; tTest = tTest15
  ; mannWhitney = mannWhitney15
  ; kruskalWallis = kruskalWallis15
  ; pearsonCorrelation = pearsonCorrelation15
  ; spearmanCorrelation = spearmanCorrelation15
  ; regression = regression15
  ; factorAnalysis = factorAnalysis15
  ; pca = pca15
  ; cluster = cluster15
  }

pairwiseInference15 : PrimeCarrier15 → PrimeCarrier15 → PairwiseModelInput
pairwiseInference15 = pairwiseModelInput15
