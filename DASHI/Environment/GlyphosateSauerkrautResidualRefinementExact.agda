module DASHI.Environment.GlyphosateSauerkrautResidualRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Environment.GlyphosateSauerkrautBioremediationBidiExact as Kraut

------------------------------------------------------------------------
-- THEOREM-BEARING RESIDUAL REFINEMENT
--
-- The companion owner upgrades the receipt-level approximation layer in
-- GlyphosateSauerkrautBioremediationBidiExact to a literal interval order.
-- Missing experimental controls may therefore be back-propagated as an
-- admissible uncertainty fibre and monotonically narrowed when independent
-- information arrives.  Narrowing is deliberately orthogonal to causal
-- mechanism identification.
------------------------------------------------------------------------

infix 4 _≤ᴺ_

data _≤ᴺ_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ᴺ n
  s≤s : {m n : Nat} → m ≤ᴺ n → suc m ≤ᴺ suc n

≤ᴺ-refl : {n : Nat} → n ≤ᴺ n
≤ᴺ-refl {zero} = z≤n
≤ᴺ-refl {suc n} = s≤s ≤ᴺ-refl

≤ᴺ-trans : {a b c : Nat} → a ≤ᴺ b → b ≤ᴺ c → a ≤ᴺ c
≤ᴺ-trans z≤n q = z≤n
≤ᴺ-trans (s≤s p) (s≤s q) = s≤s (≤ᴺ-trans p q)

record NatEnvelope : Set where
  constructor natEnvelope
  field
    lower : Nat
    upper : Nat
    lower≤upper : lower ≤ᴺ upper
    quantityReference : String
    scaleUnitReference : String

open NatEnvelope public

-- `child Refines parent` means the child admits no value outside the parent:
-- the lower edge may move upward and the upper edge may move downward.
record _Refines_ (child parent : NatEnvelope) : Set where
  constructor refines
  field
    lowerNarrows : lower parent ≤ᴺ lower child
    upperNarrows : upper child ≤ᴺ upper parent

open _Refines_ public

refinesRefl : (a : NatEnvelope) → a Refines a
refinesRefl a = refines ≤ᴺ-refl ≤ᴺ-refl

refinesTrans :
  {a b c : NatEnvelope} →
  a Refines b →
  b Refines c →
  a Refines c
refinesTrans ab bc = refines
  (≤ᴺ-trans (lowerNarrows bc) (lowerNarrows ab))
  (≤ᴺ-trans (upperNarrows ab) (upperNarrows bc))

------------------------------------------------------------------------
-- Exact arithmetic closure for the published Shiocton TEG specimen.
-- Values use the 0.01 ng/g scale inherited from the source owner:
--
--   207.26 - 26.59 = 180.67 ng/g
--
-- represented as
--
--   18067 + 2659 = 20726.
--
-- This establishes only the gross observed difference.  It does not establish
-- that all 180.67 ng/g-equivalent loss was caused by RSKJ.
------------------------------------------------------------------------

shioctonGrossDifference : Nat
shioctonGrossDifference = 18067

shioctonGrossDifferenceCloses :
  shioctonGrossDifference + 2659 ≡ 20726
shioctonGrossDifferenceCloses = refl

shioctonGrossCausalEnvelope : NatEnvelope
shioctonGrossCausalEnvelope = natEnvelope
  0
  shioctonGrossDifference
  z≤n
  "incremental RSKJ-attributable contribution consistent with gross Shiocton TEG decline"
  "0.01 ng/g-equivalent contribution"

------------------------------------------------------------------------
-- A backward refinement is valid only when its numerical interval is nested
-- inside the prior interval and every removed uncertainty component has an
-- independent provenance/derivation receipt.
------------------------------------------------------------------------

record ResidualRefinementReceipt
    (prior posterior : NatEnvelope) : Set where
  constructor residualRefinementReceipt
  field
    numericalRefinement : posterior Refines prior
    independentlyBoundedResidualReference : String
    commonScaleAndUnitReference : String
    materialInputLedgerReference : String
    environmentalCovariateReference : String
    assayErrorReference : String
    unresolvedResidualReference : String
    heldOutValidationReference : String

open ResidualRefinementReceipt public

composeResidualRefinement :
  {a b c : NatEnvelope} →
  ResidualRefinementReceipt b a →
  ResidualRefinementReceipt c b →
  String → String → String → String → String → String → String →
  ResidualRefinementReceipt c a
composeResidualRefinement ab bc independentRef commonScale materialInput environmental assay residual validation =
  residualRefinementReceipt
    (refinesTrans (numericalRefinement bc) (numericalRefinement ab))
    independentRef
    commonScale
    materialInput
    environmental
    assay
    residual
    validation

------------------------------------------------------------------------
-- Causal-budget carrier.
--
-- Known quantities can constrain pieces of the gross observation budget, but
-- the closure equation is not a decomposition theorem unless the individual
-- components themselves have independent identification receipts.
------------------------------------------------------------------------

record ResidualBudget : Set where
  constructor residualBudget
  field
    treatmentAssociated : Nat
    nonTreatmentExplained : Nat
    stillUnresolved : Nat
    grossObservedDifference : Nat
    closesObservedBudget :
      treatmentAssociated + nonTreatmentExplained + stillUnresolved
      ≡ grossObservedDifference
    scaleUnitReference : String
    componentAuthorityReference : String

open ResidualBudget public

-- The trivial initial budget deliberately places all observed loss in the
-- treatment-associated *ceiling* while claiming zero identified subtraction.
-- Subsequent receipts may reallocate/bound components, but cannot exceed the
-- gross observation envelope.
shioctonInitialBudget : ResidualBudget
shioctonInitialBudget = residualBudget
  shioctonGrossDifference
  0
  0
  shioctonGrossDifference
  refl
  "0.01 ng/g-equivalent contribution"
  "gross observation only; no component-level causal identification"

------------------------------------------------------------------------
-- Refinement is not promotion.
------------------------------------------------------------------------

record ApproximateBackpropagationState : Set where
  constructor approximateBackpropagationState
  field
    envelope : NatEnvelope
    inferenceStatus : Kraut.InferenceStatus
    statusIsApproximate : inferenceStatus ≡ Kraut.approximatelyConstrained
    residualReference : String

open ApproximateBackpropagationState public

shioctonInitialApproximateState : ApproximateBackpropagationState
shioctonInitialApproximateState = approximateBackpropagationState
  shioctonGrossCausalEnvelope
  Kraut.approximatelyConstrained
  refl
  "time, indigenous microbiome, weather/moisture, assay, new-input and sorption residuals remain open"

refinementPreservesApproximateStatus :
  {prior posterior : NatEnvelope} →
  ResidualRefinementReceipt posterior prior →
  ApproximateBackpropagationState →
  String →
  ApproximateBackpropagationState
refinementPreservesApproximateStatus {posterior = posterior} refinement priorState residual =
  approximateBackpropagationState
    posterior
    Kraut.approximatelyConstrained
    refl
    residual

narrowingCannotByItselfIdentifyMechanism :
  {prior posterior : NatEnvelope} →
  ResidualRefinementReceipt posterior prior →
  Kraut.approximatelyConstrained ≡ Kraut.exactlyMechanismIdentified →
  ⊥
narrowingCannotByItselfIdentifyMechanism refinement = Kraut.approximateNotExact

------------------------------------------------------------------------
-- Research-design consequence.
--
-- The object to shrink is therefore an admissible causal fibre, not a Boolean
-- verdict.  Controls, time-series observations, soil covariates, microbiome
-- assays, material-input ledgers, sorption measurements and analytical error
-- models can each narrow the fibre independently.  A mechanism promotion still
-- requires its own identification receipt after the interval is narrow.
------------------------------------------------------------------------

record ResidualResearchTarget : Set where
  constructor residualResearchTarget
  field
    targetEnvelope : NatEnvelope
    nextMeasurementReference : String
    expectedResidualConstrainedReference : String
    experimentDesignReference : String
    mechanismPromotionStillSeparateReference : String

open ResidualResearchTarget public
