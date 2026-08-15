module DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Terence Tao;
-- Jean-Michel Bony; DASHI repository contributors.
-- Title: "Exact absolute dyadic geometry for the three periodic
-- Navier-Stokes frequency legs".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; UCLA Math 247B lecture notes, 2007; Annales scientifiques
-- de l'Ecole Normale Superieure 14 (1981); DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; Tao's lecture notes have no DOI;
-- 10.24033/asens.1404; repository-original class predicates have no DOI.
-- Uses: one canonical absolute shell geometry before any frozen-leg rotation,
-- a far threshold G=3, a hard-shell comparable width W=1, and a separate
-- transition span of exactly two shell steps.
-- Relationship: removes the earlier farLow/farHigh naming ambiguity.  It does
-- not yet assert that every resonant repository triad satisfies exactly one
-- class; that requires the exact shell owner, zero-mode and cutoff bridges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)

farGap : Nat
farGap = 3

nearWidth : Nat
nearWidth = 1

transitionSpan : Nat
transitionSpan = 2

data PhysicalLeg : Set where
  leftLeg rightLeg outputLeg : PhysicalLeg

data FrozenView : Set where
  outputView firstAdjointView secondAdjointView : FrozenView

data OrderedPiece : Set where
  unsplitPiece directPiece swappedPiece : OrderedPiece

data GeometryTag : Set where
  leftLowTag rightLowTag outputLowTag comparableTag transitionTag residualTag :
    GeometryTag

record LeftLow (jLeft jRight jOutput : Nat) : Set where
  constructor left-low
  field
    belowRight : jLeft + farGap ≤ jRight
    belowOutput : jLeft + farGap ≤ jOutput

record RightLow (jLeft jRight jOutput : Nat) : Set where
  constructor right-low
  field
    belowLeft : jRight + farGap ≤ jLeft
    belowOutput : jRight + farGap ≤ jOutput

record OutputLow (jLeft jRight jOutput : Nat) : Set where
  constructor output-low
  field
    belowLeft : jOutput + farGap ≤ jLeft
    belowRight : jOutput + farGap ≤ jRight

record PairwiseWithinOne (jLeft jRight jOutput : Nat) : Set where
  constructor within-one
  field
    leftBelowRight : jLeft ≤ jRight + nearWidth
    rightBelowLeft : jRight ≤ jLeft + nearWidth
    leftBelowOutput : jLeft ≤ jOutput + nearWidth
    outputBelowLeft : jOutput ≤ jLeft + nearWidth
    rightBelowOutput : jRight ≤ jOutput + nearWidth
    outputBelowRight : jOutput ≤ jRight + nearWidth

record PairwiseWithinTwo (jLeft jRight jOutput : Nat) : Set where
  constructor within-two
  field
    leftBelowRight : jLeft ≤ jRight + transitionSpan
    rightBelowLeft : jRight ≤ jLeft + transitionSpan
    leftBelowOutput : jLeft ≤ jOutput + transitionSpan
    outputBelowLeft : jOutput ≤ jLeft + transitionSpan
    rightBelowOutput : jRight ≤ jOutput + transitionSpan
    outputBelowRight : jOutput ≤ jRight + transitionSpan

record TransitionGeometry (jLeft jRight jOutput : Nat) : Set where
  constructor transition
  field
    withinTwo : PairwiseWithinTwo jLeft jRight jOutput
    notWithinOne : PairwiseWithinOne jLeft jRight jOutput → ⊥
    notLeftSeparated : LeftLow jLeft jRight jOutput → ⊥
    notRightSeparated : RightLow jLeft jRight jOutput → ⊥
    notOutputSeparated : OutputLow jLeft jRight jOutput → ⊥

record ComparableGeometry (jLeft jRight jOutput : Nat) : Set where
  constructor comparable
  field
    withinOne : PairwiseWithinOne jLeft jRight jOutput

record SeparatedGeometry (jLeft jRight jOutput : Nat) : Set where
  constructor separated
  field
    lowLeg : PhysicalLeg
    leftEvidence : lowLeg ≡ leftLeg → LeftLow jLeft jRight jOutput
    rightEvidence : lowLeg ≡ rightLeg → RightLow jLeft jRight jOutput
    outputEvidence : lowLeg ≡ outputLeg → OutputLow jLeft jRight jOutput

data ResidualSubtype : Set where
  baseShell : ResidualSubtype
  shellEndpoint : ResidualSubtype
  cubicEuclideanCutoffEdge : ResidualSubtype
  zeroModeEdge : ResidualSubtype
  topCutoffTruncation : ResidualSubtype

record ResidualGeometry (jLeft jRight jOutput : Nat) : Set where
  constructor residual
  field
    subtype : ResidualSubtype

record CanonicalGeometryPartition : Set₁ where
  field
    classify : Nat → Nat → Nat → GeometryTag

    leftTagSound : ∀ jLeft jRight jOutput →
      classify jLeft jRight jOutput ≡ leftLowTag →
      LeftLow jLeft jRight jOutput

    rightTagSound : ∀ jLeft jRight jOutput →
      classify jLeft jRight jOutput ≡ rightLowTag →
      RightLow jLeft jRight jOutput

    outputTagSound : ∀ jLeft jRight jOutput →
      classify jLeft jRight jOutput ≡ outputLowTag →
      OutputLow jLeft jRight jOutput

    comparableTagSound : ∀ jLeft jRight jOutput →
      classify jLeft jRight jOutput ≡ comparableTag →
      ComparableGeometry jLeft jRight jOutput

    transitionTagSound : ∀ jLeft jRight jOutput →
      classify jLeft jRight jOutput ≡ transitionTag →
      TransitionGeometry jLeft jRight jOutput

    classesPairwiseDisjoint : Set
    classesExhaustResonantTriples : Set

open CanonicalGeometryPartition public

farGapIsThree : farGap ≡ 3
farGapIsThree = refl

nearWidthIsOne : nearWidth ≡ 1
nearWidthIsOne = refl

transitionSpanIsTwo : transitionSpan ≡ 2
transitionSpanIsTwo = refl

canonicalAbsolutePredicatesDefined : Bool
canonicalAbsolutePredicatesDefined = true

canonicalAbsolutePredicatesDefinedIsTrue :
  canonicalAbsolutePredicatesDefined ≡ true
canonicalAbsolutePredicatesDefinedIsTrue = refl

orderedPairPieceSplitDefined : Bool
orderedPairPieceSplitDefined = true

orderedPairPieceSplitDefinedIsTrue : orderedPairPieceSplitDefined ≡ true
orderedPairPieceSplitDefinedIsTrue = refl

fullRepositoryGeometryPartitionClosed : Bool
fullRepositoryGeometryPartitionClosed = false

fullRepositoryGeometryPartitionClosedIsFalse :
  fullRepositoryGeometryPartitionClosed ≡ false
fullRepositoryGeometryPartitionClosedIsFalse = refl
