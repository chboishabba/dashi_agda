{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116119NormalizedExpectationDerivativeRound281Exact where

------------------------------------------------------------------------
-- ROUND281 / SOURCE-NATIVE NORMALIZED EXPECTATION DERIVATIVE ROUTE
--
-- The shortest source-facing route to a connected two-point response is not a
-- new all-observable clustering theorem.  CMP119 already expands numerator and
-- denominator of a normalized local expectation together, while CMP116 says
-- finite declared source derivatives preserve the independent spatial/tree
-- exponential majorant.  Generic normalized-source calculus identifies the
-- mixed log response with connected covariance.
--
-- This owner separates those SOURCE-IMPORTED facts from the only literal YM
-- weld still required: the selected observable pair must be the same two CMP116
-- source directions whose localized derivative response is being bounded.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Flow
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceSpatialShellRound279Exact as R279

------------------------------------------------------------------------
-- Published source-shaped localization interface.
--
-- `localizedMixedSourceResponse` is the CMP116/CMP119 derivative of a normalized
-- insertion expansion after differentiating in a second declared J-coordinate.
-- The theorem below is represented at exactly the downstream scalar shell type:
-- no field Hessian is identified with a source Hessian.
------------------------------------------------------------------------

record CMP116119PublishedTwoSourceLocalization
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    localizedMixedSourceResponse : Scale → Volume → Root → Nat → ℚ

    localizedMixedSourceResponseBelowSpatialMark :
      ∀ scale volume root depth →
      localizedMixedSourceResponse scale volume root depth
      ≤ Shared.markedAnalyticShell shared Shared.hessianMark
          scale volume root depth

open CMP116119PublishedTwoSourceLocalization public

------------------------------------------------------------------------
-- Literal same-density source-direction weld.
--
-- The algebraic identity is not stored as a second assumption: it is compiled
-- from `LiteralTwoSourceInsertionMeaning`.  The only response identification is
-- that the literal mixed log-J derivative, after magnitude/shell organization,
-- is the SAME published localized derivative response at the support distance.
------------------------------------------------------------------------

record LiteralTwoSourceNormalizedExpectationWeld
    {Scale Volume Root Observable Scalar : Set}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    (published : CMP116119PublishedTwoSourceLocalization Scale Volume Root)
    (meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus Scalar)
    : Set₁ where
  field
    rootOfPair : Observable → Observable → Root
    physicalDistance : Observable → Observable → Nat

    magnitude : Scalar → ℚ
    connectedCovarianceMagnitude :
      Scale → Volume → Observable → Observable → ℚ

    connectedMagnitudeMeaning : ∀ scale volume left right →
      connectedCovarianceMagnitude scale volume left right
      ≡ magnitude (Cumulant.connectedCovariance algebra left right)

    literalMixedResponseMagnitudeIsPublishedShell :
      ∀ scale volume left right →
      magnitude
        (Cumulant.literalMixedSecondLogDerivative meaning
          (Cumulant.sourceDirectionOf meaning left)
          (Cumulant.sourceDirectionOf meaning right))
      ≡ localizedMixedSourceResponse published scale volume
          (rootOfPair left right) (physicalDistance left right)

open LiteralTwoSourceNormalizedExpectationWeld public

covarianceMagnitudeIsPublishedShell :
  ∀ {Scale Volume Root Observable Scalar}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus Scalar} →
  (weld : LiteralTwoSourceNormalizedExpectationWeld published meaning) →
  ∀ scale volume left right →
  connectedCovarianceMagnitude weld scale volume left right
  ≡ localizedMixedSourceResponse published scale volume
      (rootOfPair weld left right) (physicalDistance weld left right)
covarianceMagnitudeIsPublishedShell
    {algebra = algebra} {meaning = meaning} weld scale volume left right =
  trans
    (connectedMagnitudeMeaning weld scale volume left right)
    (trans
      (sym
        (congMagnitude
          (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
            meaning left right)))
      (literalMixedResponseMagnitudeIsPublishedShell weld
        scale volume left right))
  where
  congMagnitude : ∀ {x y} → x ≡ y → magnitude weld x ≡ magnitude weld y
  congMagnitude refl = refl

asRound279SpatialShell :
  ∀ {Scale Volume Root Observable Scalar}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus Scalar} →
  LiteralTwoSourceNormalizedExpectationWeld published meaning →
  R279.CMP116TwoSourceSpatialShell Scale Volume Root Observable
asRound279SpatialShell {published = published} weld = record
  { R279.CMP116TwoSourceSpatialShell.shared = shared published
  ; R279.CMP116TwoSourceSpatialShell.rootOfPair = rootOfPair weld
  ; R279.CMP116TwoSourceSpatialShell.physicalDistance = physicalDistance weld
  ; R279.CMP116TwoSourceSpatialShell.twoSourceConnectedShell =
      localizedMixedSourceResponse published
  ; R279.CMP116TwoSourceSpatialShell.connectedCovarianceMagnitude =
      connectedCovarianceMagnitude weld
  ; R279.CMP116TwoSourceSpatialShell.covarianceIsTwoSourceShell =
      covarianceMagnitudeIsPublishedShell weld
  ; R279.CMP116TwoSourceSpatialShell.twoSourceShellBelowHessianMarkedAnalytic =
      localizedMixedSourceResponseBelowSpatialMark published
  }

round281NormalizedCrossNumeratorCompilerLevel : ProofLevel
round281NormalizedCrossNumeratorCompilerLevel =
  Cross.normalizedExpectationCrossNumeratorLevel

round281ConnectedCumulantCompilerLevel : ProofLevel
round281ConnectedCumulantCompilerLevel =
  Cumulant.twoSourceConnectedCumulantCompilerLevel

round281CMP116FiniteDerivativeLocalizationLevel : ProofLevel
round281CMP116FiniteDerivativeLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round281CMP119NormalizedExpectationSourceLevel : ProofLevel
round281CMP119NormalizedExpectationSourceLevel =
  Flow.cmp116CMP119CompatibleExpectationSourceLevel

-- Source theorem: normalized local insertions differentiated in a second
-- declared J-coordinate retain the same independent hessian/spatial mark.
-- This is published/source-imported analysis, not a new DASHI physical estimate.
round281PublishedTwoSourceLocalizationLevel : ProofLevel
round281PublishedTwoSourceLocalizationLevel = standardImported

-- Remaining literal YM seam: select the actual pair of gauge-invariant local
-- observables, map each to the literal CMP116/CMP119 J-coordinate on the SAME
-- density, and identify its support/root distance with the shell organization.
round281LiteralObservablePairToSourceDirectionsLevel : ProofLevel
round281LiteralObservablePairToSourceDirectionsLevel = conditional

-- Once the source theorem and literal pair weld are supplied, R279 is compiled;
-- no separate covariance-decay theorem remains on this route.
round281ToR279CompilerLevel : ProofLevel
round281ToR279CompilerLevel = machineChecked
