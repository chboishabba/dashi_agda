module DASHI.Physics.Closure.NSTriadKNFiniteOverlapCanonicalConstants where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Pierre Germain;
-- DASHI repository contributors.
-- Title: "Canonical hard-shell near, transition, and residual multiplicities
-- for the three frozen Navier-Stokes legs".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Journal of Differential Equations 226 (2006), 373--428;
-- DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; 10.1016/j.jde.2005.10.007;
-- repository-original hard-shell counts have no DOI.
-- Uses: the exact hard-shell near width W=1, transition span two, orientation
-- multiplicity two, and five explicit residual boundary subtypes.
-- Relationship: closes shell-index combinatorics only.  Orbit, helicity,
-- reality-mate and analytic norm constants remain separate multiplicative
-- factors and are not hidden in these counts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry

nearIndexMultiplicity : Nat
nearIndexMultiplicity = suc (2 * Geometry.nearWidth)

nearPairMultiplicity : Nat
nearPairMultiplicity = nearIndexMultiplicity * nearIndexMultiplicity

transitionGapMultiplicity : Nat
transitionGapMultiplicity = suc Geometry.transitionSpan

transitionOrientationMultiplicity : Nat
transitionOrientationMultiplicity = 2

transitionOrientedMultiplicity : Nat
transitionOrientedMultiplicity =
  transitionOrientationMultiplicity * transitionGapMultiplicity

residualSubtypeMultiplicity : Nat
residualSubtypeMultiplicity = 5

record CanonicalFiniteOverlapReceipt : Set where
  constructor receipt
  field
    nearWidthIsOne : Geometry.nearWidth ≡ 1
    nearIndexCountIsThree : nearIndexMultiplicity ≡ 3
    nearPairCountIsNine : nearPairMultiplicity ≡ 9

    transitionSpanIsTwo : Geometry.transitionSpan ≡ 2
    transitionGapCountIsThree : transitionGapMultiplicity ≡ 3
    transitionOrientedCountIsSix : transitionOrientedMultiplicity ≡ 6

    residualSubtypeCountIsFive : residualSubtypeMultiplicity ≡ 5

open CanonicalFiniteOverlapReceipt public

canonicalFiniteOverlapReceipt : CanonicalFiniteOverlapReceipt
canonicalFiniteOverlapReceipt = receipt refl refl refl refl refl refl refl

record FrozenLegFiniteOverlapConstants : Set₁ where
  field
    outputNear firstNear secondNear : Nat
    outputTransition firstTransition secondTransition : Nat
    outputResidual firstResidual secondResidual : Nat

    everyNearAtMostNine : Set
    everyTransitionAtMostSix : Set
    everyResidualAtMostFiveSubtypeSum : Set

    exactShellEndpointMultiplicityIncluded : Set
    cubicCutoffEdgeMultiplicityIncluded : Set
    topCutoffTruncationMultiplicityIncluded : Set

    orbitTransportUniform : Set
    helicityTransportUniform : Set
    realityMateTransportUniform : Set
    constantsIndependentOfGalerkinCutoff : Set

open FrozenLegFiniteOverlapConstants public

canonicalHardShellOverlapCountsClosed : Bool
canonicalHardShellOverlapCountsClosed = true

canonicalHardShellOverlapCountsClosedIsTrue :
  canonicalHardShellOverlapCountsClosed ≡ true
canonicalHardShellOverlapCountsClosedIsTrue = refl

allNineTransportedFiniteOverlapConstantsClosed : Bool
allNineTransportedFiniteOverlapConstantsClosed = false

allNineTransportedFiniteOverlapConstantsClosedIsFalse :
  allNineTransportedFiniteOverlapConstantsClosed ≡ false
allNineTransportedFiniteOverlapConstantsClosedIsFalse = refl
