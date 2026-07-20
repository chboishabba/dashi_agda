module DASHI.Physics.YangMills.BalabanOneStepPolymerEstimate where

------------------------------------------------------------------------
-- Quantitative one-step polymer estimate.
--
-- The effective remainder is split into the five contributions which occur in
-- the background-field RG calculation.  Component estimates are combined by a
-- checked ordered-additive argument; the analytic estimates of the components
-- remain explicit inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedAdditiveBudget (Bound : Set) : Set₁ where
  field
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)

open OrderedAdditiveBudget public

componentTotal :
  ∀ {Bound : Set} →
  OrderedAdditiveBudget Bound →
  Bound → Bound → Bound → Bound → Bound → Bound
componentTotal order background jacobian determinant bch localization =
  add order background
    (add order jacobian
      (add order determinant
        (add order bch localization)))

componentsBelowBudget :
  ∀ {Bound : Set} →
  (order : OrderedAdditiveBudget Bound) →
  ∀ {background backgroundBudget
     jacobian jacobianBudget
     determinant determinantBudget
     bch bchBudget
     localization localizationBudget} →
  LessEqual order background backgroundBudget →
  LessEqual order jacobian jacobianBudget →
  LessEqual order determinant determinantBudget →
  LessEqual order bch bchBudget →
  LessEqual order localization localizationBudget →
  LessEqual order
    (componentTotal order background jacobian determinant bch localization)
    (componentTotal order backgroundBudget jacobianBudget determinantBudget
      bchBudget localizationBudget)
componentsBelowBudget order backgroundBound jacobianBound determinantBound
    bchBound localizationBound =
  addMonotone order backgroundBound
    (addMonotone order jacobianBound
      (addMonotone order determinantBound
        (addMonotone order bchBound localizationBound)))

record OneStepPolymerEstimateData
    (Field Polymer Bound : Set) : Set₁ where
  field
    order : OrderedAdditiveBudget Bound
    outputPolymer : Field → Polymer
    polymerNorm : Polymer → Bound

    backgroundContribution : Field → Bound
    jacobianContribution : Field → Bound
    determinantContribution : Field → Bound
    bchContribution : Field → Bound
    localizationContribution : Field → Bound

    backgroundBudget : Bound
    jacobianBudget : Bound
    determinantBudget : Bound
    bchBudget : Bound
    localizationBudget : Bound

    outputBelowComponents : ∀ configuration →
      LessEqual order
        (polymerNorm (outputPolymer configuration))
        (componentTotal order
          (backgroundContribution configuration)
          (jacobianContribution configuration)
          (determinantContribution configuration)
          (bchContribution configuration)
          (localizationContribution configuration))

    backgroundControlled : ∀ configuration →
      LessEqual order (backgroundContribution configuration) backgroundBudget
    jacobianControlled : ∀ configuration →
      LessEqual order (jacobianContribution configuration) jacobianBudget
    determinantControlled : ∀ configuration →
      LessEqual order (determinantContribution configuration) determinantBudget
    bchControlled : ∀ configuration →
      LessEqual order (bchContribution configuration) bchBudget
    localizationControlled : ∀ configuration →
      LessEqual order (localizationContribution configuration) localizationBudget

open OneStepPolymerEstimateData public

oneStepPolymerBudget :
  ∀ {Field Polymer Bound : Set} →
  OneStepPolymerEstimateData Field Polymer Bound → Bound
oneStepPolymerBudget dataSet =
  componentTotal (order dataSet)
    (backgroundBudget dataSet)
    (jacobianBudget dataSet)
    (determinantBudget dataSet)
    (bchBudget dataSet)
    (localizationBudget dataSet)

oneStepPolymerEstimate :
  ∀ {Field Polymer Bound : Set} →
  (dataSet : OneStepPolymerEstimateData Field Polymer Bound) →
  ∀ configuration →
  LessEqual (order dataSet)
    (polymerNorm dataSet (outputPolymer dataSet configuration))
    (oneStepPolymerBudget dataSet)
oneStepPolymerEstimate dataSet configuration =
  transitive (order dataSet)
    (outputBelowComponents dataSet configuration)
    (componentsBelowBudget (order dataSet)
      (backgroundControlled dataSet configuration)
      (jacobianControlled dataSet configuration)
      (determinantControlled dataSet configuration)
      (bchControlled dataSet configuration)
      (localizationControlled dataSet configuration))

record OneStepPolymerEstimateCertificate
    (Field Polymer Bound : Set) : Set₁ where
  field
    dataSet : OneStepPolymerEstimateData Field Polymer Bound
    bound : Bound
    boundIsComponentBudget : bound ≡ oneStepPolymerBudget dataSet
    outputBounded : ∀ configuration →
      LessEqual (order dataSet)
        (polymerNorm dataSet (outputPolymer dataSet configuration)) bound

assembleOneStepPolymerEstimate :
  ∀ {Field Polymer Bound : Set} →
  (dataSet : OneStepPolymerEstimateData Field Polymer Bound) →
  OneStepPolymerEstimateCertificate Field Polymer Bound
assembleOneStepPolymerEstimate dataSet = record
  { dataSet = dataSet
  ; bound = oneStepPolymerBudget dataSet
  ; boundIsComponentBudget = refl
  ; outputBounded = oneStepPolymerEstimate dataSet
  }

oneStepPolymerEstimateBridgeLevel : ProofLevel
oneStepPolymerEstimateBridgeLevel = machineChecked

oneStepPolymerComponentInputsLevel : ProofLevel
oneStepPolymerComponentInputsLevel = conditional
