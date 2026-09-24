{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalSeparationRound450Exact where

------------------------------------------------------------------------
-- B / ROUND450: PHYSICAL EUCLIDEAN SEPARATION ON THE PREFERRED R444 PATH.
--
-- The selected distance on the source-faithful path is simply
--
--   ymGraphDist leftMark rightMark.
--
-- R390 already proves antitonicity of halfPower.  Therefore B6 requires only
--
--   Euclidean time <= ymGraphDist(leftMark,rightMark).
--
-- No R435/global-tree adapter and no equality of physical distances is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact as R390
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record CanonicalPhysicalSeparation
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    : Set where
  field
    euclideanTime : Nat

    timeBelowSelectedGraphDistance :
      euclideanTime Nat.≤
      Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data)

open CanonicalPhysicalSeparation public

selectedHalfDecayBelowEuclideanTime :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (physical : CanonicalPhysicalSeparation data) →
  Geo.halfPower
    (Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data))
  ≤
  Geo.halfPower (euclideanTime physical)
selectedHalfDecayBelowEuclideanTime physical =
  R390.halfPowerAntitone
    (timeBelowSelectedGraphDistance physical)

round450PhysicalDecayTransportLevel : ProofLevel
round450PhysicalDecayTransportLevel = R390.round390DistanceLowerCompilerLevel

-- B6 is now only the physical support-separation statement above.
literalRound450EuclideanSupportSeparationLevel : ProofLevel
literalRound450EuclideanSupportSeparationLevel = conditional
