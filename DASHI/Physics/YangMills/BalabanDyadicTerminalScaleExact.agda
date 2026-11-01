module DASHI.Physics.YangMills.BalabanDyadicTerminalScaleExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact using
  (pow2)

------------------------------------------------------------------------
-- Exact normalized dyadic terminal scale.
--
-- Start with lattice spacing 2^-N and use block factor two at every RG step.
-- After exactly N steps the represented physical spacing is
--
--   2^N / 2^N = 1.
--
-- Ratios are represented by numerator/denominator pairs, so the theorem is a
-- kernel equality and does not need division, logarithms, or Archimedean choice.
-- Matching this normalized schedule to the physical running coupling remains a
-- separate dimensional-transmutation theorem.
------------------------------------------------------------------------

record ScaleRatio : Set where
  constructor scaleRatio
  field
    numerator denominator : Nat

open ScaleRatio public

initialDyadicSpacing : Nat → ScaleRatio
initialDyadicSpacing exponent = scaleRatio (suc zero) (pow2 exponent)

spacingAfterSteps : Nat → Nat → ScaleRatio
spacingAfterSteps exponent steps =
  scaleRatio (pow2 steps) (pow2 exponent)

terminalDyadicSpacing : Nat → ScaleRatio
terminalDyadicSpacing exponent = spacingAfterSteps exponent exponent

unitScale : ScaleRatio
unitScale = scaleRatio (suc zero) (suc zero)

RatioEqual : ScaleRatio → ScaleRatio → Set
RatioEqual left right =
  numerator left * denominator right
  ≡ numerator right * denominator left

ratioEqualReflexive : ∀ ratio → RatioEqual ratio ratio
ratioEqualReflexive ratio = refl

terminalDyadicSpacingIsUnit : ∀ exponent →
  RatioEqual (terminalDyadicSpacing exponent) unitScale
terminalDyadicSpacingIsUnit exponent =
  trans
    (ℕP.*-identityʳ (pow2 exponent))
    (sym (ℕP.*-identityˡ (pow2 exponent)))

record BoundedTerminalScale (schedule : Nat → ScaleRatio) : Set where
  field
    terminalStep : Nat → Nat
    lowerBound upperBound : ScaleRatio
    terminalAboveLower : ∀ exponent →
      RatioEqual (schedule (terminalStep exponent)) lowerBound
    terminalBelowUpper : ∀ exponent →
      RatioEqual (schedule (terminalStep exponent)) upperBound

open BoundedTerminalScale public

normalizedDyadicSchedule : Nat → ScaleRatio
normalizedDyadicSchedule exponent = terminalDyadicSpacing exponent

normalizedDyadicTerminalScaleBounded :
  BoundedTerminalScale normalizedDyadicSchedule
normalizedDyadicTerminalScaleBounded = record
  { terminalStep = λ exponent → exponent
  ; lowerBound = unitScale
  ; upperBound = unitScale
  ; terminalAboveLower = terminalDyadicSpacingIsUnit
  ; terminalBelowUpper = terminalDyadicSpacingIsUnit
  }

------------------------------------------------------------------------
-- Carrier adapter for a selected physical spacing type.
--
-- The difficult running-coupling theorem is represented by one coherent match
-- between the physical terminal spacing and the dyadic ratio.  Once that match
-- is supplied, equality with the interpreted unit scale and a bounded terminal
-- package are derived rather than assumed again downstream.
------------------------------------------------------------------------

record PhysicalDyadicTerminalScaleMatch (Bound : Set) : Set₁ where
  field
    EqualBound : Bound → Bound → Set
    equalBoundTransitive : ∀ {left middle right} →
      EqualBound left middle → EqualBound middle right → EqualBound left right

    interpretRatio : ScaleRatio → Bound
    terminalPhysicalSpacing : Nat → Bound

    ratioEqualityPreserved : ∀ {left right} →
      RatioEqual left right →
      EqualBound (interpretRatio left) (interpretRatio right)

    physicalTerminalMatchesDyadic : ∀ exponent →
      EqualBound
        (terminalPhysicalSpacing exponent)
        (interpretRatio (terminalDyadicSpacing exponent))

open PhysicalDyadicTerminalScaleMatch public

physicalTerminalSpacingIsUnit :
  ∀ {Bound} (matching : PhysicalDyadicTerminalScaleMatch Bound) exponent →
  EqualBound matching
    (terminalPhysicalSpacing matching exponent)
    (interpretRatio matching unitScale)
physicalTerminalSpacingIsUnit matching exponent =
  equalBoundTransitive matching
    (physicalTerminalMatchesDyadic matching exponent)
    (ratioEqualityPreserved matching
      (terminalDyadicSpacingIsUnit exponent))

record BoundedPhysicalTerminalScale
    {Bound : Set}
    (matching : PhysicalDyadicTerminalScaleMatch Bound) : Set₁ where
  field
    physicalLower physicalUpper : Bound
    terminalAtLower : ∀ exponent →
      EqualBound matching
        (terminalPhysicalSpacing matching exponent)
        physicalLower
    terminalAtUpper : ∀ exponent →
      EqualBound matching
        (terminalPhysicalSpacing matching exponent)
        physicalUpper

open BoundedPhysicalTerminalScale public

boundedPhysicalTerminalScaleFromDyadic :
  ∀ {Bound} (matching : PhysicalDyadicTerminalScaleMatch Bound) →
  BoundedPhysicalTerminalScale matching
boundedPhysicalTerminalScaleFromDyadic matching = record
  { physicalLower = interpretRatio matching unitScale
  ; physicalUpper = interpretRatio matching unitScale
  ; terminalAtLower = physicalTerminalSpacingIsUnit matching
  ; terminalAtUpper = physicalTerminalSpacingIsUnit matching
  }

normalizedDyadicTerminalSpacingLevel : ProofLevel
normalizedDyadicTerminalSpacingLevel = machineChecked

physicalTerminalScaleAdapterAssemblyLevel : ProofLevel
physicalTerminalScaleAdapterAssemblyLevel = machineChecked

physicalRunningCouplingToDyadicScheduleLevel : ProofLevel
physicalRunningCouplingToDyadicScheduleLevel = conditional

dimensionalTransmutationScaleMatchingLevel : ProofLevel
dimensionalTransmutationScaleMatchingLevel = conjectural
