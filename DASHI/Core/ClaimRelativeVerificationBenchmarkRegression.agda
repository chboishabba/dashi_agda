module DASHI.Core.ClaimRelativeVerificationBenchmarkRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)

import DASHI.Core.ClaimRelativeVerificationSOTAAtlasExact as SOTA
import DASHI.Core.ClaimRelativeVerificationBenchmarkExact as Benchmark
import DASHI.Core.ClaimRelativeVerificationFixtureExact as Fixture

sotaBoundary : SOTA.ClaimRelativeVerificationSOTABoundary
sotaBoundary = SOTA.canonicalClaimRelativeVerificationSOTABoundary

externalSourceDoesNotCreateRepoTheorem :
  SOTA.externalSourceMentionCreatesDASHITheorem sotaBoundary ≡ false
externalSourceDoesNotCreateRepoTheorem = refl

reportedMetricDoesNotCreateGeneralLaw :
  SOTA.reportedMetricCreatesGeneralLaw sotaBoundary ≡ false
reportedMetricDoesNotCreateGeneralLaw = refl

benchmarkBoundary : Benchmark.ClaimRelativeVerificationBenchmarkBoundary
benchmarkBoundary = Benchmark.canonicalClaimRelativeVerificationBenchmarkBoundary

postHocAbstentionRejected :
  Benchmark.postHocAbstentionCountsAsSuccessfulAbstention benchmarkBoundary ≡ false
postHocAbstentionRejected = refl

pairedActAbstainRequired :
  Benchmark.abstentionEvaluationUsesPairedActAbstainCases benchmarkBoundary ≡ true
pairedActAbstainRequired = refl

singleAggregateNotEnough :
  Benchmark.singleAggregateScoreDeterminesReliability benchmarkBoundary ≡ false
singleAggregateNotEnough = refl

sameConsumerRequired :
  Benchmark.comparatorMayChangeDeclaredConsumer benchmarkBoundary ≡ false
sameConsumerRequired = refl

fixtureBenchmark :
  Benchmark.ClaimRelativeVerificationBenchmark
    Fixture.problem
    Fixture.Source Fixture.Specification Fixture.Consumer
    Fixture.Object Fixture.Intervention Fixture.Repair Fixture.Training
    Fixture.HeldOut Fixture.Prediction
    Fixture.ValidatorObservation Fixture.ConsumerObservation
fixtureBenchmark = Fixture.benchmark

pairedFixtureCorrect : Benchmark.PairedCorrect Fixture.pairedResult
pairedFixtureCorrect = Fixture.pairedResultCorrect
