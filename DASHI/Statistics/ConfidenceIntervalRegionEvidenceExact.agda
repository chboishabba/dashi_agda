module DASHI.Statistics.ConfidenceIntervalRegionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Statistics.HypothesisRegionGeometryExact as Region

------------------------------------------------------------------------
-- CONFIDENCE-INTERVAL / REGION EVIDENCE
--
-- This owner does not assign confidence levels or sampling semantics.  It owns
-- only the geometric handoff used after a statistically justified interval has
-- already been produced: a whole interval may license a region-relative claim
-- only through an explicit containment receipt.
------------------------------------------------------------------------

record OrderedIntervalGeometry (Parameter : Set) : Set₁ where
  constructor ordered-interval-geometry
  field
    _≤_ : Parameter → Parameter → Set
    reflexive : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    antisymmetric : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    orderReference : String

open OrderedIntervalGeometry public

record ConfidenceInterval
    {Parameter : Set}
    (order : OrderedIntervalGeometry Parameter) : Set where
  constructor confidence-interval
  field
    lower : Parameter
    upper : Parameter
    valid : _≤_ order lower upper
    intervalReference : String

open ConfidenceInterval public

Within :
  ∀ {Parameter : Set}
    {order : OrderedIntervalGeometry Parameter} →
  ConfidenceInterval order → Parameter → Set
Within {order = order} interval x =
  _≤_ order (lower interval) x × _≤_ order x (upper interval)

IntervalContainedIn :
  ∀ {Parameter : Set}
    {order : OrderedIntervalGeometry Parameter} →
  ConfidenceInterval order → (Parameter → Set) → Set
IntervalContainedIn interval predicate =
  ∀ {x} → Within interval x → predicate x

record IntervalRegionEvidence
    {Parameter : Set}
    {order : OrderedIntervalGeometry Parameter}
    (geometry : Region.HypothesisRegionGeometry Parameter)
    (interval : ConfidenceInterval order) : Set₁ where
  constructor interval-region-evidence
  field
    positiveContainment : Set
    centreContainment : Set
    negativeContainment : Set

    positiveSound :
      positiveContainment →
      IntervalContainedIn interval (Region.PositiveRegion geometry)

    centreSound :
      centreContainment →
      IntervalContainedIn interval (Region.CentreRegion geometry)

    negativeSound :
      negativeContainment →
      IntervalContainedIn interval (Region.NegativeRegion geometry)

open IntervalRegionEvidence public

data IntervalEvidenceDisposition
    {Parameter : Set}
    {order : OrderedIntervalGeometry Parameter}
    {geometry : Region.HypothesisRegionGeometry Parameter}
    {interval : ConfidenceInterval order}
    (evidence : IntervalRegionEvidence geometry interval) : Trit → Set where
  intervalPositive :
    positiveContainment evidence →
    IntervalEvidenceDisposition evidence pos
  intervalCentre :
    centreContainment evidence →
    IntervalEvidenceDisposition evidence zer
  intervalNegative :
    negativeContainment evidence →
    IntervalEvidenceDisposition evidence neg

------------------------------------------------------------------------
-- Firewalls.  Failure of whole-interval containment is not containment in the
-- opposite region, and touching/containing a point of a region is weaker than
-- whole-interval containment in that region.
------------------------------------------------------------------------

data NotContainedPositiveMeansNegativePermission : Set where

data NotContainedNegativeMeansPositivePermission : Set where

data ContainsCentrePointMeansCentreContainedPermission : Set where

data IntervalOverlapMeansDirectionalEvidencePermission : Set where

notContainedPositiveDoesNotMeanNegative :
  NotContainedPositiveMeansNegativePermission → ⊥
notContainedPositiveDoesNotMeanNegative ()

notContainedNegativeDoesNotMeanPositive :
  NotContainedNegativeMeansPositivePermission → ⊥
notContainedNegativeDoesNotMeanPositive ()

containsCentrePointDoesNotMeanCentreContained :
  ContainsCentrePointMeansCentreContainedPermission → ⊥
containsCentrePointDoesNotMeanCentreContained ()

intervalOverlapDoesNotByItselfLicenseDirection :
  IntervalOverlapMeansDirectionalEvidencePermission → ⊥
intervalOverlapDoesNotByItselfLicenseDirection ()

record ConfidenceIntervalRegionBoundary : Set where
  constructor confidence-interval-region-boundary
  field
    wholeIntervalContainmentCanLicenseRegionEvidence : Bool
    failedPositiveContainmentIsNegativeEvidence : Bool
    failedNegativeContainmentIsPositiveEvidence : Bool
    containingOneCentrePointProvesWholeCentreContainment : Bool
    overlapAloneLicensesDirectionalEvidence : Bool

canonicalConfidenceIntervalRegionBoundary : ConfidenceIntervalRegionBoundary
canonicalConfidenceIntervalRegionBoundary =
  confidence-interval-region-boundary true false false false false
