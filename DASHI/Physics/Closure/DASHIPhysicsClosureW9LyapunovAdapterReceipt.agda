module DASHI.Physics.Closure.DASHIPhysicsClosureW9LyapunovAdapterReceipt where

-- W9: lane-rank pressure adapter for the MDL/Lyapunov pressure interface.
--
-- This surface is deliberately narrow.  It records the finite gauge-lane
-- pressure budget supplied by the promoted lane-dimension table and pairs it
-- with the existing weightedMaxPressure <= weightedSupport receipt.  It does
-- not alter terminal, Clay, Qcore, or canonical dim-15 compatibility flags.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _≤_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)

import DASHI.Arithmetic.MaxPressure as Max
import DASHI.Arithmetic.WeightedPressure as Weighted
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane
import DASHI.Physics.Closure.W9WeightedSupportRetargetConsumerReceipt as W9Support
import DASHI.Physics.Moonshine.LaneDimensionTheoremReceiptSurface as LaneDimension

data W9LaneRankPressureAdapterStatus : Set where
  laneRankPressureBudgetComputed :
    W9LaneRankPressureAdapterStatus

data W9LaneRankGaugePrime : Set where
  gaugeP2 gaugeP3 gaugeP5 gaugeP7 :
    W9LaneRankGaugePrime

gaugePrimeToMonsterPrime :
  W9LaneRankGaugePrime →
  PrimeLane.MonsterPrimeLane
gaugePrimeToMonsterPrime gaugeP2 =
  PrimeLane.p2
gaugePrimeToMonsterPrime gaugeP3 =
  PrimeLane.p3
gaugePrimeToMonsterPrime gaugeP5 =
  PrimeLane.p5
gaugePrimeToMonsterPrime gaugeP7 =
  PrimeLane.p7

laneRank :
  PrimeLane.MonsterPrimeLane →
  Nat
laneRank =
  LaneDimension.orbifoldWeightOneLieAlgebraRank

laneAdjointPressureContribution :
  PrimeLane.MonsterPrimeLane →
  Nat
laneAdjointPressureContribution =
  LaneDimension.orbifoldWeightOneLieAlgebraDimension

gaugeLaneRank :
  W9LaneRankGaugePrime →
  Nat
gaugeLaneRank p =
  laneRank (gaugePrimeToMonsterPrime p)

gaugeLaneAdjointPressureContribution :
  W9LaneRankGaugePrime →
  Nat
gaugeLaneAdjointPressureContribution p =
  laneAdjointPressureContribution (gaugePrimeToMonsterPrime p)

rank2Is0 :
  gaugeLaneRank gaugeP2 ≡ 0
rank2Is0 =
  refl

rank3Is1 :
  gaugeLaneRank gaugeP3 ≡ 1
rank3Is1 =
  refl

rank5Is2 :
  gaugeLaneRank gaugeP5 ≡ 2
rank5Is2 =
  refl

rank7Is1 :
  gaugeLaneRank gaugeP7 ≡ 1
rank7Is1 =
  refl

adjointPressure2Is0 :
  gaugeLaneAdjointPressureContribution gaugeP2 ≡ 0
adjointPressure2Is0 =
  refl

adjointPressure3Is3 :
  gaugeLaneAdjointPressureContribution gaugeP3 ≡ 3
adjointPressure3Is3 =
  refl

adjointPressure5Is8 :
  gaugeLaneAdjointPressureContribution gaugeP5 ≡ 8
adjointPressure5Is8 =
  refl

adjointPressure7Is3 :
  gaugeLaneAdjointPressureContribution gaugeP7 ≡ 3
adjointPressure7Is3 =
  refl

gaugeLaneAdjointPressureSum :
  Nat
gaugeLaneAdjointPressureSum =
  gaugeLaneAdjointPressureContribution gaugeP2
  + gaugeLaneAdjointPressureContribution gaugeP3
  + gaugeLaneAdjointPressureContribution gaugeP5
  + gaugeLaneAdjointPressureContribution gaugeP7

gaugeLaneAdjointPressureSumIs14 :
  gaugeLaneAdjointPressureSum ≡ 14
gaugeLaneAdjointPressureSumIs14 =
  refl

record W9MDLLyapunovPressureBoundAdapter : Setω where
  field
    pressureBound :
      Nat

    pressureBoundIsGaugeAdjointSum :
      pressureBound ≡ gaugeLaneAdjointPressureSum

    pressureBoundIs14 :
      pressureBound ≡ 14

    laneRankWitness :
      W9LaneRankGaugePrime →
      Nat

    laneRankWitnessIsCanonical :
      laneRankWitness ≡ gaugeLaneRank

    lanePressureWitness :
      W9LaneRankGaugePrime →
      Nat

    lanePressureWitnessIsAdjointDimension :
      lanePressureWitness ≡ gaugeLaneAdjointPressureContribution

    p2Rank0 :
      laneRankWitness gaugeP2 ≡ 0

    p3Rank1 :
      laneRankWitness gaugeP3 ≡ 1

    p5Rank2 :
      laneRankWitness gaugeP5 ≡ 2

    p7Rank1 :
      laneRankWitness gaugeP7 ≡ 1

    p2Pressure0 :
      lanePressureWitness gaugeP2 ≡ 0

    p3Pressure3 :
      lanePressureWitness gaugeP3 ≡ 3

    p5Pressure8 :
      lanePressureWitness gaugeP5 ≡ 8

    p7Pressure3 :
      lanePressureWitness gaugeP7 ≡ 3

    weightedMaxPressure≤weightedSupport :
      ∀ x y →
        Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

    weightedSupportRetargetReceipt :
      W9Support.WeightedSupportRetargetConsumerReceipt

    status :
      W9LaneRankPressureAdapterStatus

    w9PressureCompatible :
      Bool

    w9PressureCompatible-v :
      w9PressureCompatible ≡ true

    terminalClaimPromoted :
      Bool

    terminalClaimPromoted-v :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromoted-v :
      continuumClayMassGapPromoted ≡ false

    nonPromotionBoundary :
      List String

open W9MDLLyapunovPressureBoundAdapter public

w9LyapunovAdapter :
  W9MDLLyapunovPressureBoundAdapter
w9LyapunovAdapter =
  record
    { pressureBound =
        14
    ; pressureBoundIsGaugeAdjointSum =
        refl
    ; pressureBoundIs14 =
        refl
    ; laneRankWitness =
        gaugeLaneRank
    ; laneRankWitnessIsCanonical =
        refl
    ; lanePressureWitness =
        gaugeLaneAdjointPressureContribution
    ; lanePressureWitnessIsAdjointDimension =
        refl
    ; p2Rank0 =
        refl
    ; p3Rank1 =
        refl
    ; p5Rank2 =
        refl
    ; p7Rank1 =
        refl
    ; p2Pressure0 =
        refl
    ; p3Pressure3 =
        refl
    ; p5Pressure8 =
        refl
    ; p7Pressure3 =
        refl
    ; weightedMaxPressure≤weightedSupport =
        Max.weightedMaxPressure≤weightedSupport
    ; weightedSupportRetargetReceipt =
        W9Support.canonicalWeightedSupportRetargetConsumerReceipt
    ; status =
        laneRankPressureBudgetComputed
    ; w9PressureCompatible =
        true
    ; w9PressureCompatible-v =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromoted-v =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromoted-v =
        refl
    ; nonPromotionBoundary =
        "Records only the W9 lane-rank pressure budget 0+3+8+3=14"
        ∷ "Uses DLM lane rank table p2=0, p3=1, p5=2, p7=1"
        ∷ "Pairs the rank budget with the existing weightedMaxPressure <= weightedSupport receipt"
        ∷ "Does not construct CancellationPressureCompatibility, canonical Qcore equality, terminal promotion, or Clay promotion"
        ∷ []
    }

w9KillReceipt :
  W9MDLLyapunovPressureBoundAdapter
w9KillReceipt =
  w9LyapunovAdapter

w9LaneRankPressureBoundIs14 :
  pressureBound w9LyapunovAdapter ≡ 14
w9LaneRankPressureBoundIs14 =
  refl
