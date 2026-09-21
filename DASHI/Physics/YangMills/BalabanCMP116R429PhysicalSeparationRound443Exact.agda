{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429PhysicalSeparationRound443Exact where

------------------------------------------------------------------------
-- B / ROUND443: R429 SELECTED SUPPORT DISTANCE -> PHYSICAL/TIME DECAY.
--
-- R390 already proves halfPower is antitone:
--
--     near <= far  ==>  (1/2)^far <= (1/2)^near.
--
-- R435 already makes the selected connecting distance the concrete support
-- graph distance between the two literal source marks.  Hence the Goal-1 B6
-- decay calibration needs only the physical one-sided geometry
--
--     Euclidean time <= selected support distance.
--
-- No equality of distances and no new exponential comparison theorem is
-- required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as R416
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact as R390
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

selectedConnectingDistance :
  ∀ {Measure TestObservable dataSet extension base fourStage} →
  R435.CanonicalSelectedBSource
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage →
  Nat
selectedConnectingDistance selected =
  R411.selectedConnectingDistance
    (R416.asR411SelectedSupportConnectionGeometry
      (R435.supportGraph selected))

record R429SelectedPhysicalSeparation
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ.ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (selected : R435.CanonicalSelectedBSource fourStage)
    : Set where
  field
    euclideanTime : Nat

    -- The sole physical B6 geometry payment.
    timeBelowSelectedSupportDistance :
      euclideanTime Nat.≤ selectedConnectingDistance selected

open R429SelectedPhysicalSeparation public

selectedHalfDecayBelowEuclideanTime :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    {selected :
      R435.CanonicalSelectedBSource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage}
    (physical : R429SelectedPhysicalSeparation selected) →
  Geo.halfPower (selectedConnectingDistance selected)
  ≤
  Geo.halfPower (euclideanTime physical)
selectedHalfDecayBelowEuclideanTime physical =
  R390.halfPowerAntitone
    (timeBelowSelectedSupportDistance physical)

round443HalfDecayTransportLevel : ProofLevel
round443HalfDecayTransportLevel = R390.round390DistanceLowerCompilerLevel

-- B6 is reduced to a single source/physical support statement:
-- Euclidean separation is no larger than the literal selected support-graph
-- distance.  All decreasing-decay transport after that is compiler-owned.
literalRound443PhysicalSupportSeparationLevel : ProofLevel
literalRound443PhysicalSupportSeparationLevel = conditional
