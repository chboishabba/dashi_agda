module DASHI.Biology.ReachableSectorEntropyExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Raw syntactic configurations are distinguished from states reachable by
-- declared object-level moves.  A forbidden manipulation is reified as a
-- typed meta-level transition with an explicit violation witness.

data RawConfiguration : Set where
  coherentNegative : RawConfiguration
  coherentMediated : RawConfiguration
  coherentPositive : RawConfiguration
  arbitrarilyDisassembled : RawConfiguration

data ReachableConfiguration : Set where
  reachableNegative : ReachableConfiguration
  reachableMediated : ReachableConfiguration
  reachablePositive : ReachableConfiguration

embedReachable : ReachableConfiguration → RawConfiguration
embedReachable reachableNegative = coherentNegative
embedReachable reachableMediated = coherentMediated
embedReachable reachablePositive = coherentPositive

data ObjectMove : Set where
  moveNegativeToMediated : ObjectMove
  moveMediatedToNegative : ObjectMove
  moveMediatedToPositive : ObjectMove
  movePositiveToMediated : ObjectMove

data ViolationKind : Set where
  directPoleJump : ViolationKind
  arbitraryComponentManipulation : ViolationKind
  carrierTypeMismatch : ViolationKind

record ViolationWitness : Set where
  constructor violationWitness
  field
    source : RawConfiguration
    target : RawConfiguration
    violationKind : ViolationKind

open ViolationWitness public

data TransitionResult : Set where
  legalTransition : ReachableConfiguration → TransitionResult
  typedViolation : ViolationWitness → TransitionResult

applyObjectMove : ObjectMove → ReachableConfiguration → TransitionResult
applyObjectMove moveNegativeToMediated reachableNegative =
  legalTransition reachableMediated
applyObjectMove moveNegativeToMediated state =
  typedViolation
    (violationWitness
      (embedReachable state)
      coherentMediated
      carrierTypeMismatch)
applyObjectMove moveMediatedToNegative reachableMediated =
  legalTransition reachableNegative
applyObjectMove moveMediatedToNegative state =
  typedViolation
    (violationWitness
      (embedReachable state)
      coherentNegative
      carrierTypeMismatch)
applyObjectMove moveMediatedToPositive reachableMediated =
  legalTransition reachablePositive
applyObjectMove moveMediatedToPositive state =
  typedViolation
    (violationWitness
      (embedReachable state)
      coherentPositive
      carrierTypeMismatch)
applyObjectMove movePositiveToMediated reachablePositive =
  legalTransition reachableMediated
applyObjectMove movePositiveToMediated state =
  typedViolation
    (violationWitness
      (embedReachable state)
      coherentMediated
      carrierTypeMismatch)

directNegativeToPositive : TransitionResult
directNegativeToPositive =
  typedViolation
    (violationWitness
      coherentNegative
      coherentPositive
      directPoleJump)

arbitraryDisassembly : TransitionResult
arbitraryDisassembly =
  typedViolation
    (violationWitness
      coherentMediated
      arbitrarilyDisassembled
      arbitraryComponentManipulation)

negativeToMediatedIsLegal :
  applyObjectMove moveNegativeToMediated reachableNegative
  ≡ legalTransition reachableMediated
negativeToMediatedIsLegal = refl

directPoleJumpCarriesWitness :
  directNegativeToPositive
  ≡ typedViolation
      (violationWitness coherentNegative coherentPositive directPoleJump)
directPoleJumpCarriesWitness = refl

------------------------------------------------------------------------
-- Accessible-sector ceilings.  The exact finite carrier count is checked;
-- logarithmic Shannon entropy belongs to a later probability layer.

rawConfigurationCount : Nat
rawConfigurationCount = 4

reachableConfigurationCount : Nat
reachableConfigurationCount = 3

rawMinusReachableIsOne :
  rawConfigurationCount ∸ reachableConfigurationCount ≡ 1
rawMinusReachableIsOne = refl

record AccessibleSectorCeiling : Set where
  constructor accessibleSectorCeiling
  field
    rawStateCount : Nat
    accessibleStateCount : Nat
    excludedStateCount : Nat
    countCertificate :
      accessibleStateCount + excludedStateCount ≡ rawStateCount

open AccessibleSectorCeiling public

canonicalAccessibleSectorCeiling : AccessibleSectorCeiling
canonicalAccessibleSectorCeiling =
  accessibleSectorCeiling 4 3 1 refl

------------------------------------------------------------------------
-- Context can change the legal sector without changing the raw syntax.

data ConstraintRegime : Set where
  mediatedRegime : ConstraintRegime
  unrestrictedRegime : ConstraintRegime
  quarantineRegime : ConstraintRegime

accessibleCount : ConstraintRegime → Nat
accessibleCount mediatedRegime = 3
accessibleCount unrestrictedRegime = 4
accessibleCount quarantineRegime = 1

mediatedCeilingBelowUnrestricted :
  accessibleCount unrestrictedRegime ∸ accessibleCount mediatedRegime ≡ 1
mediatedCeilingBelowUnrestricted = refl

quarantineCeilingIsOne : accessibleCount quarantineRegime ≡ 1
quarantineCeilingIsOne = refl

record ReachableSectorBoundary : Set where
  constructor reachableSectorBoundary
  field
    everyRawConfigurationIsObjectLevelReachable : Bool
    everyRawConfigurationIsObjectLevelReachableIsFalse :
      everyRawConfigurationIsObjectLevelReachable ≡ false

    violationWitnessIsAnOrdinaryLegalMove : Bool
    violationWitnessIsAnOrdinaryLegalMoveIsFalse :
      violationWitnessIsAnOrdinaryLegalMove ≡ false

    stateCountAloneIsShannonEntropy : Bool
    stateCountAloneIsShannonEntropyIsFalse :
      stateCountAloneIsShannonEntropy ≡ false

    symmetryAndConstraintsCanLowerAccessibleCeiling : Bool
    symmetryAndConstraintsCanLowerAccessibleCeilingIsTrue :
      symmetryAndConstraintsCanLowerAccessibleCeiling ≡ true

open ReachableSectorBoundary public

canonicalReachableSectorBoundary : ReachableSectorBoundary
canonicalReachableSectorBoundary =
  reachableSectorBoundary false refl false refl false refl true refl
