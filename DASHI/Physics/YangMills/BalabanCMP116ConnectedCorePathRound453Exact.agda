{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ConnectedCorePathRound453Exact where

------------------------------------------------------------------------
-- B / ROUND453: CMP116 CONNECTED CORE PATH -> DOMAIN-SPECIFIC DISTANCE.
--
-- CMP116 Sect. 1 constructs Y_0 as the connected component containing the
-- distinguished cube before the auxiliary fibre sums are performed.  The
-- source-faithful B4 payment is therefore a path theorem, not a full-domain
-- polymer injection:
--
--   for each retained Y, the selected left/right source marks are joined by a
--   valid support-graph path inside the corresponding connected core, and
--
--   pathLength <= d_k(Y).
--
-- Graph-distance minimality then gives
--
--   ymGraphDist(left,right) <= d_k(Y),
--
-- which is exactly the single geometry field consumed by R448.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Nat.Base as Nat
open import Data.Nat.Properties using (≤-trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448

record ConnectedCorePathGeometry
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    : Set₁ where
  field
    connectedCorePath :
      R444.Domain data →
      Graph.Path Graph.currentFiniteSupportGraph

    connectedCorePathStartsAtLeft :
      ∀ domain →
      Graph.Path.start (connectedCorePath domain)
      ≡ R444.leftMark data

    connectedCorePathEndsAtRight :
      ∀ domain →
      Graph.Path.finish (connectedCorePath domain)
      ≡ R444.rightMark data

    connectedCorePathValid :
      ∀ domain →
      Graph.Path.valid (connectedCorePath domain) ≡ true

    connectedCorePathLengthBelowSourceDistance :
      ∀ domain →
      Graph.Path.pathLength (connectedCorePath domain)
      Nat.≤ Source.sourceTreeDistance (R444.source data) domain

open ConnectedCorePathGeometry public

graphDistanceBelowSourceTreeDistance :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      ConnectedCorePathGeometry
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  ∀ domain →
  Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data)
  Nat.≤
  Source.sourceTreeDistance (R444.source data) domain
graphDistanceBelowSourceTreeDistance geometry domain =
  ≤-trans
    (Graph.graphDistMinimalityViaImportedFiniteGraphDistanceAxiom
      (connectedCorePath geometry domain)
      (connectedCorePathStartsAtLeft geometry domain)
      (connectedCorePathEndsAtRight geometry domain)
      (connectedCorePathValid geometry domain))
    (connectedCorePathLengthBelowSourceDistance geometry domain)

asCanonicalDomainSpecificRateSplit :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  ConnectedCorePathGeometry data →
  R448.CanonicalDomainSpecificRateSplit data
asCanonicalDomainSpecificRateSplit data geometry = record
  { R448.CanonicalDomainSpecificRateSplit.sourceTreeDistanceDominatesSelectedGraphDistance =
      graphDistanceBelowSourceTreeDistance geometry
  }

round453GraphMinimalityCompilerLevel : ProofLevel
round453GraphMinimalityCompilerLevel = machineChecked

round453R448GeometryCompilerLevel : ProofLevel
round453R448GeometryCompilerLevel = machineChecked

-- Preferred B4 is now exactly the connected-core path construction plus its
-- length comparison with the source d_k(Y).  Full R429-domain injectivity into
-- a repository polymer is not required on this route.
literalRound453CMP116ConnectedCorePathLevel : ProofLevel
literalRound453CMP116ConnectedCorePathLevel = conditional
