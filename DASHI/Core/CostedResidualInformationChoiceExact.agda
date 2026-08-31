module DASHI.Core.CostedResidualInformationChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice

------------------------------------------------------------------------
-- COSTED PARTIAL-INFORMATION SELECTION
--
-- A useful information move need not close the current consumer or identify a
-- mechanism.  It may instead carry a certified refinement of the admissible
-- residual fibre.  Quantitative "gain" is application-declared/certified rather
-- than invented from arbitrary Set-valued fibre cardinalities.
------------------------------------------------------------------------

record ResidualInformationMove (Hidden : Set) : Set₁ where
  constructor residualInformationMove
  field
    prior : Bidi.ResidualFibre Hidden
    posterior : Bidi.ResidualFibre Hidden
    refinement : Bidi.FibreRefines posterior prior

    moveKind : Choice.InformationMoveKind
    cost : Nat
    certifiedGain : Nat

    moveReference : String
    gainCertificateReference : String
    calibrationReference : String
    admissibilityReference : String
    residualStillOpenReference : String

open ResidualInformationMove public

asInformationMove :
  ∀ {Hidden} → ResidualInformationMove Hidden → Choice.InformationMove
asInformationMove move = Choice.informationMove
  (moveKind move)
  (cost move)
  (moveReference move)
  (calibrationReference move)
  (admissibilityReference move)

------------------------------------------------------------------------
-- Thresholded progress: optimize cost only after a declared minimum useful
-- residual reduction has been met.
------------------------------------------------------------------------

record MeetsResidualGainThreshold
    {Hidden : Set}
    (move : ResidualInformationMove Hidden)
    (threshold : Nat) : Set where
  constructor meetsResidualGainThreshold
  field
    gainEnough : threshold ≤ certifiedGain move

open MeetsResidualGainThreshold public

record CheapestThresholdResidualMove
    {Hidden : Set}
    (threshold : Nat)
    (Declared : ResidualInformationMove Hidden → Set) : Set₂ where
  constructor cheapestThresholdResidualMove
  field
    selected : ResidualInformationMove Hidden
    selectedDeclared : Declared selected
    selectedMeetsThreshold : MeetsResidualGainThreshold selected threshold

    minimalCost :
      (alternative : ResidualInformationMove Hidden) →
      Declared alternative →
      MeetsResidualGainThreshold alternative threshold →
      cost selected ≤ cost alternative

    comparisonReference : String
    consumerReference : String

open CheapestThresholdResidualMove public

------------------------------------------------------------------------
-- Pareto-style dominance without division or probability semantics.
------------------------------------------------------------------------

record ResidualMoveDominates
    {Hidden : Set}
    (left right : ResidualInformationMove Hidden) : Set where
  constructor residualMoveDominates
  field
    noMoreCost : cost left ≤ cost right
    noLessCertifiedGain : certifiedGain right ≤ certifiedGain left

open ResidualMoveDominates public

record ResidualParetoChoice
    {Hidden : Set}
    (Declared : ResidualInformationMove Hidden → Set) : Set₂ where
  constructor residualParetoChoice
  field
    selected : ResidualInformationMove Hidden
    selectedDeclared : Declared selected
    undominated :
      (alternative : ResidualInformationMove Hidden) →
      Declared alternative →
      ResidualMoveDominates alternative selected →
      ResidualMoveDominates selected alternative
    comparisonReference : String

open ResidualParetoChoice public

------------------------------------------------------------------------
-- Crucial authority boundary.
------------------------------------------------------------------------

data ResidualMoveOutcomeGrade : Set where
  partialResidualProgress
  consumerClosed
  exactMechanismIdentified
  theoremProved
  : ResidualMoveOutcomeGrade

partialProgressNotConsumerClosure :
  partialResidualProgress ≡ consumerClosed → ⊥
partialProgressNotConsumerClosure ()

partialProgressNotMechanismIdentification :
  partialResidualProgress ≡ exactMechanismIdentified → ⊥
partialProgressNotMechanismIdentification ()

partialProgressNotTheoremProof :
  partialResidualProgress ≡ theoremProved → ⊥
partialProgressNotTheoremProof ()

record CostedResidualChoiceBoundary : Set where
  constructor costedResidualChoiceBoundary
  field
    arbitraryFibreCardinalityIsAssumed : Bool
    arbitraryFibreCardinalityIsAssumedIsFalse :
      arbitraryFibreCardinalityIsAssumed ≡ false
    certifiedGainMayBeApplicationSpecific : Bool
    certifiedGainMayBeApplicationSpecificIsTrue :
      certifiedGainMayBeApplicationSpecific ≡ true
    cheapestMoveWithoutProgressWitnessIsPreferred : Bool
    cheapestMoveWithoutProgressWitnessIsPreferredIsFalse :
      cheapestMoveWithoutProgressWitnessIsPreferred ≡ false
    partialResidualProgressIsProof : Bool
    partialResidualProgressIsProofIsFalse :
      partialResidualProgressIsProof ≡ false
    costAndGainCanDefineAParetoSurface : Bool
    costAndGainCanDefineAParetoSurfaceIsTrue :
      costAndGainCanDefineAParetoSurface ≡ true

canonicalCostedResidualChoiceBoundary : CostedResidualChoiceBoundary
canonicalCostedResidualChoiceBoundary =
  costedResidualChoiceBoundary
    false refl true refl false refl false refl true refl
