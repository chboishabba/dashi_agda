module DASHI.Statistics.HypothesisRegionGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- HYPOTHESIS-REGION GEOMETRY
--
-- A balanced trit is only meaningful after an inferential axis has been typed.
-- This owner therefore separates:
--   * the scientific parameter/effect carrier;
--   * three declared regions on that carrier;
--   * the statistical result;
--   * the soundness bridge from a result into a region-relative disposition.
--
-- In particular, the centre need not mean literal equality with zero.  It can be
-- an indifference band, equivalence region, unresolved region, or any other
-- declared middle region appropriate to the design.
------------------------------------------------------------------------

record HypothesisRegionGeometry (Parameter : Set) : Set₁ where
  constructor hypothesis-region-geometry
  field
    PositiveRegion : Parameter → Set
    CentreRegion : Parameter → Set
    NegativeRegion : Parameter → Set

    positiveCentreDisjoint :
      ∀ {x} → PositiveRegion x → CentreRegion x → ⊥
    positiveNegativeDisjoint :
      ∀ {x} → PositiveRegion x → NegativeRegion x → ⊥
    centreNegativeDisjoint :
      ∀ {x} → CentreRegion x → NegativeRegion x → ⊥

    positiveReference : String
    centreReference : String
    negativeReference : String

open HypothesisRegionGeometry public

------------------------------------------------------------------------
-- A scientific claim axis is not identified with a test decision.  The
-- hypothesis carrier keeps the proposition under interpretation explicit.
------------------------------------------------------------------------

record RegionIndexedHypothesis (Parameter : Set) : Set₁ where
  constructor region-indexed-hypothesis
  field
    geometry : HypothesisRegionGeometry Parameter
    parameter : Parameter
    hypothesisReference : String

open RegionIndexedHypothesis public

------------------------------------------------------------------------
-- Result interpretation is proof-bearing and geometry-relative.
------------------------------------------------------------------------

record RegionEvidenceSemantics
    (Parameter Result : Set)
    (geometry : HypothesisRegionGeometry Parameter) : Set₁ where
  constructor region-evidence-semantics
  field
    SupportsPositive : Result → Parameter → Set
    SupportsCentre : Result → Parameter → Set
    SupportsNegative : Result → Parameter → Set

    positiveSound :
      ∀ {result parameter} →
      SupportsPositive result parameter →
      PositiveRegion geometry parameter

    centreSound :
      ∀ {result parameter} →
      SupportsCentre result parameter →
      CentreRegion geometry parameter

    negativeSound :
      ∀ {result parameter} →
      SupportsNegative result parameter →
      NegativeRegion geometry parameter

open RegionEvidenceSemantics public

data RegionEvidenceDisposition
    {Parameter Result : Set}
    {geometry : HypothesisRegionGeometry Parameter}
    (semantics : RegionEvidenceSemantics Parameter Result geometry)
    (result : Result)
    (parameter : Parameter) : Trit → Set where
  positiveRegionEvidence :
    SupportsPositive semantics result parameter →
    RegionEvidenceDisposition semantics result parameter pos
  centreRegionEvidence :
    SupportsCentre semantics result parameter →
    RegionEvidenceDisposition semantics result parameter zer
  negativeRegionEvidence :
    SupportsNegative semantics result parameter →
    RegionEvidenceDisposition semantics result parameter neg

------------------------------------------------------------------------
-- The key no-go: absence from one signed region does not place a parameter in
-- the opposite signed region.  Region membership remains proof-bearing.
------------------------------------------------------------------------

data OutsidePositiveMeansNegativePermission : Set where

data OutsideNegativeMeansPositivePermission : Set where

data CentreMeansLiteralZeroPermission : Set where

outsidePositiveDoesNotMeanNegative :
  OutsidePositiveMeansNegativePermission → ⊥
outsidePositiveDoesNotMeanNegative ()

outsideNegativeDoesNotMeanPositive :
  OutsideNegativeMeansPositivePermission → ⊥
outsideNegativeDoesNotMeanPositive ()

centreNeedNotMeanLiteralZero :
  CentreMeansLiteralZeroPermission → ⊥
centreNeedNotMeanLiteralZero ()

record HypothesisRegionBoundary : Set where
  constructor hypothesis-region-boundary
  field
    axisMustBeTypedBeforeTritInterpretation : Bool
    centreAlwaysMeansLiteralParameterZero : Bool
    failureOfPositiveMembershipMeansNegativeMembership : Bool
    failureOfNegativeMembershipMeansPositiveMembership : Bool
    regionMembershipRequiresWitness : Bool

canonicalHypothesisRegionBoundary : HypothesisRegionBoundary
canonicalHypothesisRegionBoundary =
  hypothesis-region-boundary true false false false true
