module DASHI.Cognition.PNF.SensibLawWorkerScalingRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([])

import DASHI.Cognition.PNF.RuntimeThroughputConstitution as Throughput

fixtureSingleWorker :
  Throughput.WorkerScalePoint "fixture:matched-parser-workload"
fixtureSingleWorker =
  Throughput.workerScalePoint
    1
    1000
    100
    10000
    7000
    2000
    80
    120
    160
    300
    20
    100

fixtureFourWorkers :
  Throughput.WorkerScalePoint "fixture:matched-parser-workload"
fixtureFourWorkers =
  Throughput.workerScalePoint
    4
    1000
    100
    3200
    7600
    2200
    90
    150
    190
    340
    25
    110

fixtureWorkerScaling :
  Throughput.WorkerScalingReceipt "fixture:matched-parser-workload"
fixtureWorkerScaling =
  Throughput.workerScalingReceipt
    fixtureSingleWorker
    refl
    2
    fixtureFourWorkers
    refl
    []

fixtureBaselineIsOneWorker :
  Throughput.WorkerScalePoint.workerCount
    (Throughput.WorkerScalingReceipt.singleWorkerBaseline fixtureWorkerScaling)
  ≡ 1
fixtureBaselineIsOneWorker = refl

fixtureParallelPointIsFourWorkers :
  Throughput.WorkerScalePoint.workerCount
    (Throughput.WorkerScalingReceipt.parallelObservation fixtureWorkerScaling)
  ≡ 4
fixtureParallelPointIsFourWorkers = refl
