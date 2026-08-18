module DASHI.Governance.InverseJusticeThroughputExact where

------------------------------------------------------------------------
-- EXTENDED INVERSE-JUSTICE DAMAGE / THROUGHPUT
--
-- This file extends the situated fibre without collapsing justice to a scalar.
-- A Nat magnitude is local to one already-identified invariant and is used only
-- to distinguish retention of a violation from a witnessed worsening of that
-- same violation.  It is not an empirical police-harm score or legal threshold.
--
-- Source calibration is inherited from
-- DASHI.Governance.SituatedInverseJusticeFibreExact:
--   * Hanna Fenichel Pitkin, The Concept of Representation (1967), no DOI;
--   * Kimberle Williams Crenshaw, "Mapping the Margins" (1991),
--     DOI 10.2307/1229039;
--   * Washington State Access to Justice Board, "Washington State Access to
--     Justice Technology Principles" (2004), no DOI listed in repo record.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TransitionResidual as Transition

record InvariantViolationMagnitude
  {base : Justice.SituatedJusticeBase}
  (fibre : Justice.JusticeFibre base) : Set where
  constructor invariantViolationMagnitude
  field
    magnitude : Transition.ConstitutionalInvariant → Nat

open InvariantViolationMagnitude public

record WorsenedPositiveViolation
  {beforeBase afterBase : Justice.SituatedJusticeBase}
  {before : Justice.JusticeFibre beforeBase}
  {after : Justice.JusticeFibre afterBase}
  (transition : Justice.JusticeTransition before after)
  (beforeMagnitude : InvariantViolationMagnitude before)
  (afterMagnitude : InvariantViolationMagnitude after)
  (invariant : Transition.ConstitutionalInvariant) : Set where
  constructor worsenedPositiveViolation
  field
    applicableBefore : Justice.applicable before invariant
    applicableAfter : Justice.applicable after invariant
    violatedBefore :
      Justice.validation before invariant ≡ Transition.positivelyViolated
    violatedAfter :
      Justice.validation after invariant ≡ Transition.positivelyViolated
    strictlyWorsened :
      suc (magnitude beforeMagnitude invariant) ≤
      magnitude afterMagnitude invariant

record WorseningInverseJusticeOperator
  {beforeBase afterBase : Justice.SituatedJusticeBase}
  {before : Justice.JusticeFibre beforeBase}
  {after : Justice.JusticeFibre afterBase}
  (transition : Justice.JusticeTransition before after)
  (beforeMagnitude : InvariantViolationMagnitude before)
  (afterMagnitude : InvariantViolationMagnitude after) : Set₁ where
  constructor worseningInverseJusticeOperator
  field
    worsenedInvariant : Transition.ConstitutionalInvariant
    worsenedViolation :
      WorsenedPositiveViolation
        transition beforeMagnitude afterMagnitude worsenedInvariant
    noOffsettingRepair :
      (candidate : Transition.ConstitutionalInvariant) →
      Justice.RepairedPositiveViolation transition candidate → ⊥

-- The combined operator admits either creation of a new positive violation or
-- strict worsening of an already-positive violation.
data ExtendedInverseJusticeOperator
  {beforeBase afterBase : Justice.SituatedJusticeBase}
  {before : Justice.JusticeFibre beforeBase}
  {after : Justice.JusticeFibre afterBase}
  (transition : Justice.JusticeTransition before after) : Set₁ where
  createdViolationInverse :
    Justice.InverseJusticeOperator transition →
    ExtendedInverseJusticeOperator transition
  worsenedViolationInverse :
    (beforeMagnitude : InvariantViolationMagnitude before) →
    (afterMagnitude : InvariantViolationMagnitude after) →
    WorseningInverseJusticeOperator
      transition beforeMagnitude afterMagnitude →
    ExtendedInverseJusticeOperator transition

negativeJusticeDisplacementMakesCoercionInverseJustice :
  ∀ {beforeBase afterBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    {transition : Justice.JusticeTransition before after} →
  Justice.InverseJusticeOperator transition →
  ExtendedInverseJusticeOperator transition
negativeJusticeDisplacementMakesCoercionInverseJustice = createdViolationInverse

------------------------------------------------------------------------
-- Exact finite worsening witness.
------------------------------------------------------------------------

allRightsViolated :
  Transition.ConstitutionalInvariant → Transition.GovernanceValidation
allRightsViolated invariant = Transition.positivelyViolated

violatedFibreA : Justice.JusticeFibre Justice.exampleBase
violatedFibreA = Justice.justiceFibre Justice.allApplicable allRightsViolated

violatedFibreB : Justice.JusticeFibre Justice.exampleBase
violatedFibreB = Justice.justiceFibre Justice.allApplicable allRightsViolated

worseningAction : Justice.JusticeTransition violatedFibreA violatedFibreB
worseningAction = Justice.justiceTransition "same-role worsening intervention"

zeroMagnitude : InvariantViolationMagnitude violatedFibreA
zeroMagnitude = invariantViolationMagnitude (λ invariant → 0)

oneMagnitude : InvariantViolationMagnitude violatedFibreB
oneMagnitude = invariantViolationMagnitude (λ invariant → 1)

oneLeOne : 1 ≤ 1
oneLeOne = s≤s z≤n

canonicalWorsenedRightsViolation :
  WorsenedPositiveViolation
    worseningAction zeroMagnitude oneMagnitude Transition.rightsInvariant
canonicalWorsenedRightsViolation =
  worsenedPositiveViolation tt tt refl refl oneLeOne

noRepairWhenAllViolated :
  (candidate : Transition.ConstitutionalInvariant) →
  Justice.RepairedPositiveViolation worseningAction candidate → ⊥
noRepairWhenAllViolated candidate repair with
  Justice.RepairedPositiveViolation.becameSatisfied repair
... | ()

canonicalWorseningInverseJustice :
  WorseningInverseJusticeOperator worseningAction zeroMagnitude oneMagnitude
canonicalWorseningInverseJustice =
  worseningInverseJusticeOperator
    Transition.rightsInvariant
    canonicalWorsenedRightsViolation
    noRepairWhenAllViolated

worsenedPositiveViolationIsInverseJustice :
  ExtendedInverseJusticeOperator worseningAction
worsenedPositiveViolationIsInverseJustice =
  worsenedViolationInverse
    zeroMagnitude
    oneMagnitude
    canonicalWorseningInverseJustice

------------------------------------------------------------------------
-- Proof-carrying throughput.
-- "Too many coppers, not enough justice" is represented here as an accounting
-- witness only after individual transitions have already been proved
-- inverse-justice.  Raw officer/action counts never determine justice sign.
------------------------------------------------------------------------

record CoerciveJusticeThroughput : Set where
  constructor coerciveJusticeThroughput
  field
    coerciveTransitions : Nat
    inverseJusticeTransitions : Nat
    justiceRepairTransitions : Nat
    inverseContainedInCoercive :
      inverseJusticeTransitions ≤ coerciveTransitions
    inverseOutpacesRepair :
      suc justiceRepairTransitions ≤ inverseJusticeTransitions

open CoerciveJusticeThroughput public

twoLeTwo : 2 ≤ 2
twoLeTwo = s≤s (s≤s z≤n)

oneLeTwo : 1 ≤ 2
oneLeTwo = s≤s z≤n

tooManyCoppersNotEnoughJusticeWitness : CoerciveJusticeThroughput
tooManyCoppersNotEnoughJusticeWitness =
  coerciveJusticeThroughput
    2
    2
    0
    twoLeTwo
    oneLeTwo

record ThroughputBoundary : Set where
  constructor throughputBoundary
  field
    rawCoerciveCountDeterminesJusticeSign : Bool
    inverseJusticeRequiresTransitionWitness : Bool
    worseningRequiresInvariantLocalMagnitudeWitness : Bool
    inverseThroughputMayOutpaceRepair : Bool

canonicalThroughputBoundary : ThroughputBoundary
canonicalThroughputBoundary =
  throughputBoundary false true true true
