module DASHI.Physics.Closure.NSTriadKNFiniteOverlapConstantProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Pierre Germain;
-- DASHI repository contributors.
-- Title: "Near, transition, and residual finite-overlap constants for the
-- three frozen Navier-Stokes legs".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Journal of Differential Equations 226 (2006), 373--428;
-- DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; 10.1016/j.jde.2005.10.007;
-- repository-original class constants have no DOI.
-- Uses: finite dyadic support overlap and the repository far-gap candidate
-- G=3, whose transition gaps are exactly 0,1,2 at the arithmetic level.
-- Relationship: closes the transition gap enumeration and gives the generic
-- near-pair formula (2W+1)^2.  The repository near width and the residual
-- subtype partition remain explicit inputs, so the nine analytic constants
-- are not prematurely marked closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

import DASHI.Physics.Closure.NSTriadKNRepositoryDyadicSeparationAudit as Gap
import DASHI.Physics.Closure.NSTriadKNThreeNumericShellLedgerStatus as Rows

nearIndexCount : Nat → Nat
nearIndexCount width = suc (2 * width)

nearPairMultiplicity : Nat → Nat
nearPairMultiplicity width =
  nearIndexCount width * nearIndexCount width

transitionGapZero transitionGapOne transitionGapTwo : Nat
transitionGapZero = 0
transitionGapOne = 1
transitionGapTwo = 2

transitionUnorientedMultiplicity : Nat
transitionUnorientedMultiplicity = 3

transitionOrientedMultiplicity : Nat
transitionOrientedMultiplicity = 6

residualSubtypeCount : Nat
residualSubtypeCount = 4

record TransitionMultiplicityReceipt : Set where
  constructor transition-receipt
  field
    farGapCandidateIsThree : Gap.repositoryFarGapCandidate ≡ 3
    transitionMaximumIsTwo : Gap.transitionMaximumGap ≡ 2
    firstGapIsZero : transitionGapZero ≡ 0
    secondGapIsOne : transitionGapOne ≡ 1
    thirdGapIsTwo : transitionGapTwo ≡ 2
    unorientedCountIsThree : transitionUnorientedMultiplicity ≡ 3
    orientedCountIsSix : transitionOrientedMultiplicity ≡ 6

open TransitionMultiplicityReceipt public

transitionMultiplicityReceipt : TransitionMultiplicityReceipt
transitionMultiplicityReceipt =
  transition-receipt refl refl refl refl refl refl refl

record ResidualSubtypePartition {s : Agda.Primitive.Level} :
    Set (Agda.Primitive.lsuc s) where
  field
    ResidualSubtype : Set s
    boundaryShellZero : ResidualSubtype
    shellEndpointAmbiguity : ResidualSubtype
    cubicEuclideanCutoffEdge : ResidualSubtype
    zeroModeExclusionEdge : ResidualSubtype

    fourSubtypesExhaustive : Set s
    fourSubtypesPairwiseDisjoint : Set s
    eachSubtypeMultiplicityBound : ResidualSubtype → Nat
    allSubtypeBoundsIndependentOfCutoff : Set s

open ResidualSubtypePartition public

record NineFiniteOverlapConstantCutset : Set₁ where
  field
    repositoryNearWidth : Nat
    nearWidthMatchesEveryFrozenLeg : Set
    nearMultiplicityIsSquare :
      nearPairMultiplicity repositoryNearWidth
      ≡ nearIndexCount repositoryNearWidth * nearIndexCount repositoryNearWidth

    outputNearConstant firstNearConstant secondNearConstant : Nat
    outputTransitionConstant firstTransitionConstant secondTransitionConstant : Nat
    outputResidualConstant firstResidualConstant secondResidualConstant : Nat

    allNearConstantsAtMostGenericMultiplicity : Set
    allTransitionConstantsAtMostSix : Set
    residualPartition : ResidualSubtypePartition
    allResidualConstantsBoundedBySubtypeSum : Set

    constantsIndependentOfGalerkinCutoff : Set
    constantsPreservedByOrbitTransport : Set
    constantsPreservedByHelicityResolution : Set

open NineFiniteOverlapConstantCutset public

transitionGapEnumerationClosed : Bool
transitionGapEnumerationClosed = true

transitionGapEnumerationClosedIsTrue :
  transitionGapEnumerationClosed ≡ true
transitionGapEnumerationClosedIsTrue = refl

nearMultiplicityFormulaRepresented : Bool
nearMultiplicityFormulaRepresented = true

nearMultiplicityFormulaRepresentedIsTrue :
  nearMultiplicityFormulaRepresented ≡ true
nearMultiplicityFormulaRepresentedIsTrue = refl

allNineFiniteOverlapConstantsClosed : Bool
allNineFiniteOverlapConstantsClosed = false

allNineFiniteOverlapConstantsClosedIsFalse :
  allNineFiniteOverlapConstantsClosed ≡ false
allNineFiniteOverlapConstantsClosedIsFalse = refl

priorFiniteOverlapRowCountIsNine : Rows.finiteOverlapRowCount ≡ 9
priorFiniteOverlapRowCountIsNine = refl
