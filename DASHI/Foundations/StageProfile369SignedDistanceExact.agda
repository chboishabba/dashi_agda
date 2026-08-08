module DASHI.Foundations.StageProfile369SignedDistanceExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- Residues alone do not say whether a stage lies before or after a closure.
-- SignedDistance retains that orientation without introducing integers into
-- the existing natural-number closure ledger.
------------------------------------------------------------------------

data SignedDistance : Set where
  beforeClosure : Nat → SignedDistance
  atClosure : SignedDistance
  pastClosure : Nat → SignedDistance

record StageProfile369 : Set where
  constructor stage-profile369
  field
    address : BT.BalancedTernaryAddress
    value : Nat
    valueExact : BT.BalancedTernaryAddress.representedValue address ≡ value

    residue3 residue6 residue9 : Nat
    signedDistance3 signedDistance6 signedDistance9 : SignedDistance

    triadicChart : BT.ClosureProfile369
    triadicChartValueExact : BT.ClosureProfile369.value triadicChart ≡ value

open StageProfile369 public

stageFiveProfile369 : StageProfile369
stageFiveProfile369 =
  stage-profile369
    BT.fiveBalancedAddress 5 refl
    2 5 5
    (pastClosure 2) (beforeClosure 1) (beforeClosure 4)
    BT.fiveClosureProfile refl

stageSixProfile369 : StageProfile369
stageSixProfile369 =
  stage-profile369
    BT.sixBalancedAddress 6 refl
    0 0 6
    (pastClosure 3) atClosure (beforeClosure 3)
    BT.sixClosureProfile refl

stageFiveDecisionSignature :
  residue3 stageFiveProfile369 ≡ 2
  × signedDistance3 stageFiveProfile369 ≡ pastClosure 2
  × signedDistance6 stageFiveProfile369 ≡ beforeClosure 1
  × signedDistance9 stageFiveProfile369 ≡ beforeClosure 4
stageFiveDecisionSignature = refl , refl , refl , refl

stageSixDualSignature :
  signedDistance3 stageSixProfile369 ≡ pastClosure 3
  × signedDistance6 stageSixProfile369 ≡ atClosure
  × signedDistance9 stageSixProfile369 ≡ beforeClosure 3
stageSixDualSignature = refl , refl , refl

stageFiveAndSixShareRadixPrefix :
  BT.SharedPrefixWitness BT.fiveBalancedAddress BT.sixBalancedAddress
stageFiveAndSixShareRadixPrefix = BT.fiveSixSharedPrefix

record StageProfileBoundary : Set where
  constructor stage-profile-boundary
  field
    residuesAndClosureOrientationRetained : Bool
    residuesAndClosureOrientationRetainedIsTrue :
      residuesAndClosureOrientationRetained ≡ true
    equalResidueImpliesEqualStructuredState : Bool
    equalResidueImpliesEqualStructuredStateIsFalse :
      equalResidueImpliesEqualStructuredState ≡ false

canonicalStageProfileBoundary : StageProfileBoundary
canonicalStageProfileBoundary =
  stage-profile-boundary true refl false refl
