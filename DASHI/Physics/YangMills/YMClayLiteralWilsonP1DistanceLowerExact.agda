{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP1DistanceLowerExact where

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact as R313
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedDecayToR274Round387Exact as R387
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact as R390
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceTrajectoryRound280Exact as R280
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

------------------------------------------------------------------------
-- P1 WITH LEAST-PRIVILEGE SUPPORT GEOMETRY.
--
-- Exact supportDistance = time is stronger than the decreasing half-envelope
-- needs.  The finite Route-S statement follows from time <= physicalDistance.
------------------------------------------------------------------------

literalWilsonFiniteClusteringFromDistanceLower :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : R320.DirectSelectedT5MarkedDecayPayment base)
    (magnitudeIsAbsolute : ∀ value → R278.magnitude extension value ≡ Data.Rational.Base.∣ value ∣)
    (cutoff : Nat)
    (left right : TestObservable)
    (time : Nat) →
  time Nat.≤
    R274.physicalDistance
      (R387.r320PaymentAsR274ConnectedShell base payment)
      left right →
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff) left right
  ≤ Shell.quarter * Power.rationalPower Geo.half time
literalWilsonFiniteClusteringFromDistanceLower
    {dataSet = dataSet} {extension = extension}
    base payment magnitudeIsAbsolute cutoff left right time timeBelow =
  let
    shell = R387.r320PaymentAsR274ConnectedShell base payment
    distance = R274.physicalDistance shell left right
    finiteBound =
      R274.connectedCovarianceGeometricBound shell cutoff left right

    responseBelowHalfPower :
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤ Shell.quarter * Geo.halfPower distance
    responseBelowHalfPower =
      subst
        (λ rhs →
          R278.connectedCovarianceMagnitude extension
            (Gram.measureSequence dataSet cutoff) left right
          ≤ Shell.quarter * rhs)
        (Data.Relation.Binary.PropositionalEquality.sym
          (R280.halfPowerIsRationalPower distance))
        finiteBound

    geometry : R390.PhysicalDistanceLowerGeometricData
    geometry = record
      { R390.PhysicalDistanceLowerGeometricData.response =
          R278.connectedCovarianceMagnitude extension
            (Gram.measureSequence dataSet cutoff) left right
      ; R390.PhysicalDistanceLowerGeometricData.amplitude = Shell.quarter
      ; R390.PhysicalDistanceLowerGeometricData.time = time
      ; R390.PhysicalDistanceLowerGeometricData.physicalDistance = distance
      ; R390.PhysicalDistanceLowerGeometricData.amplitudeNonnegative =
          R274.quarterNonnegative
      ; R390.PhysicalDistanceLowerGeometricData.responseBelowPhysicalDistance =
          responseBelowHalfPower
      ; R390.PhysicalDistanceLowerGeometricData.timeBelowPhysicalDistance =
          timeBelow
      }

    atTime =
      R390.responseBelowTimeGeometric geometry
  in
  subst
    (λ rhs →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤ Shell.quarter * rhs)
    (R280.halfPowerIsRationalPower time)
    atTime

p1ExactDistanceEqualityRequired : Agda.Builtin.Bool.Bool
p1ExactDistanceEqualityRequired = Agda.Builtin.Bool.false

p1DistanceLowerCompilerLevel : ProofLevel
p1DistanceLowerCompilerLevel = machineChecked
