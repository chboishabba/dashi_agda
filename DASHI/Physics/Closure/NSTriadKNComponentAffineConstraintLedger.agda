module DASHI.Physics.Closure.NSTriadKNComponentAffineConstraintLedger where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; DASHI
-- repository contributors.
-- Title: "Component-level exact affine constraint ledger for the three
-- periodic Navier-Stokes Schur conditions".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Differential Equations 226 (2006), 373--428; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.1016/j.jde.2005.10.007;
-- repository-original component constraints have no DOI.
-- Uses: all twelve separated direct components, the nine finite-overlap
-- conditions, affine left/right/output weights and a strict epsilon margin.
-- Relationship: replaces the old label-only 24-row readiness summary with a
-- component ledger.  It refuses to solve the affine system until every one of
-- the five analytic archetypes has a proved numeric inequality and every
-- transported finite-overlap constant is supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNSeparatedComponentLedger as Components
import DASHI.Physics.Closure.NSTriadKNSeparatedComponentEndpointProfiles as Profiles
import DASHI.Physics.Closure.NSTriadKNFiniteOverlapCanonicalConstants as Overlap

data ConstraintOwner : Set where
  outputOwner firstAdjointOwner secondAdjointOwner : ConstraintOwner

data FiniteOverlapClass : Set where
  nearClass transitionClass residualClass : FiniteOverlapClass

record AffineWeightFunction {s : Level} (Scalar : Set s) : Set s where
  constructor affine-weight
  field
    slope intercept : Scalar

open AffineWeightFunction public

record ComponentAffineConstraint {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    component : Components.ShellComponent
    endpointProfile : Profiles.EndpointProfile

    leftCoefficient rightCoefficient outputCoefficient : Scalar
    unweightedTerm target epsilonMargin : Scalar

    componentProfileMatches :
      endpointProfile ≡ Profiles.componentEndpointProfile component
    affineIdentity : Set s
    strictEndpointSlack : Set s
    interiorStrictness : Set s

open ComponentAffineConstraint public

record FiniteOverlapAffineConstraint {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    owner : ConstraintOwner
    overlapClass : FiniteOverlapClass
    multiplicity : Nat

    leftCoefficient rightCoefficient outputCoefficient : Scalar
    target epsilonMargin : Scalar

    multiplicityMatchesCanonicalCount : Set s
    affineIdentity : Set s
    strictEndpointSlack : Set s
    interiorStrictness : Set s

open FiniteOverlapAffineConstraint public

record CompleteComponentConstraintLedger {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s

    leftWeight rightWeight outputWeight : AffineWeightFunction Scalar
    epsilon : Scalar
    epsilonStrictlyPositive : Set s

    outputSeparated :
      Components.GeometryTag → ComponentAffineConstraint Scalar
    firstDirectSeparated :
      Components.GeometryTag → ComponentAffineConstraint Scalar
    firstSwappedSeparated :
      Components.GeometryTag → ComponentAffineConstraint Scalar
    secondSeparated :
      Components.GeometryTag → ComponentAffineConstraint Scalar

    outputFiniteOverlap :
      FiniteOverlapClass → FiniteOverlapAffineConstraint Scalar
    firstFiniteOverlap :
      FiniteOverlapClass → FiniteOverlapAffineConstraint Scalar
    secondFiniteOverlap :
      FiniteOverlapClass → FiniteOverlapAffineConstraint Scalar

    onlySeparatedGeometryTagsConsumed : Set s
    twelveSeparatedComponentsCoveredExactlyOnce : Set s
    nineFiniteOverlapConditionsCoveredExactlyOnce : Set s

    fiveArchetypeNumericEstimatesConsumed : Set s
    transportedOverlapConstantsConsumed : Set s
    gapThreeRepositoryTheoremConsumed : Set s

    everyLowerEndpointSlackStrict : Set s
    everyUpperEndpointSlackStrict : Set s
    everyInteriorConstraintStrict : Set s
    minimumExactSlackAttained : Set s
    epsilonAtMostHalfMinimumSlack : Set s

open CompleteComponentConstraintLedger public

record ExactComponentAffineSolver {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    Ledger : Set (lsuc s)

    normalizeAllComponentConstraints : Set s
    evaluateLowerEndpointLimits : Set s
    evaluateUpperEndpointLimits : Set s
    solveRationalWeightCoefficients : Set s
    computeEveryExactSlack : Set s
    identifySaturatingComponent : Set s
    chooseHalfMinimumSlack : Set s
    proveEpsilonStrictlyPositive : Set s

    soundness : Set s

open ExactComponentAffineSolver public

separatedComponentCount : Nat
separatedComponentCount = 12

finiteOverlapConditionCount : Nat
finiteOverlapConditionCount = 9

minimumAnalyticArchetypeCount : Nat
minimumAnalyticArchetypeCount = 5

allSeparatedEndpointProfilesAvailable : Bool
allSeparatedEndpointProfilesAvailable =
  Profiles.allTwelveEndpointProfilesInstantiated

allSeparatedEndpointProfilesAvailableIsTrue :
  allSeparatedEndpointProfilesAvailable ≡ true
allSeparatedEndpointProfilesAvailableIsTrue =
  Profiles.allTwelveEndpointProfilesInstantiatedIsTrue

canonicalOverlapMultiplicitiesAvailable : Bool
canonicalOverlapMultiplicitiesAvailable =
  Overlap.canonicalHardShellOverlapCountsClosed

canonicalOverlapMultiplicitiesAvailableIsTrue :
  canonicalOverlapMultiplicitiesAvailable ≡ true
canonicalOverlapMultiplicitiesAvailableIsTrue =
  Overlap.canonicalHardShellOverlapCountsClosedIsTrue

completeNumericComponentConstraintLedgerClosed : Bool
completeNumericComponentConstraintLedgerClosed = false

completeNumericComponentConstraintLedgerClosedIsFalse :
  completeNumericComponentConstraintLedgerClosed ≡ false
completeNumericComponentConstraintLedgerClosedIsFalse = refl

strictComponentAffineCertificateClosed : Bool
strictComponentAffineCertificateClosed = false

strictComponentAffineCertificateClosedIsFalse :
  strictComponentAffineCertificateClosed ≡ false
strictComponentAffineCertificateClosedIsFalse = refl
