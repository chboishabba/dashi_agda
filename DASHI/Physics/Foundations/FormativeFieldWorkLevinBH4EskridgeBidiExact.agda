module DASHI.Physics.Foundations.FormativeFieldWorkLevinBH4EskridgeBidiExact where

-- Source-native interdisciplinary consumer, 2026-11-21.
-- SOURCE: Rupert Sheldrake, user-provided "Rupert Sheldrake Explains Morphic
-- Resonance (With a Galton Board)" transcript, 00:01-03:43 and 05:17-08:45:
-- his distinction between FORMATIVE and ENERGETIC causation, his attribution
-- of mechanistic reduction to the seventeenth century, and Michael Levin.
-- SOURCE: Amy Eskridge, "A Historical Perspective on Anti-Gravity Technology",
-- HAL5 (2018); candidate mechanisms and claims, not measured antigravity.
-- BH4 experimental authors and chemical sources remain attributed by their
-- original Kitzerow/NOS3/NeuralContext modules; no claim of shared physics.
-- This is original DASHI formal bookkeeping, not Sheldrake's derivation.
--
-- Crucial scientific boundary: a field may change a spatial/probabilistic
-- pattern without being a CONSUMED FUEL, yet physical forces and field energy
-- are not exempt from total energy, momentum or source/backaction accounting.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger
import DASHI.Biology.Levin.TravelingFieldControl as LevinField
import DASHI.Biology.Levin.FungalCollectiveIntelligenceCore as Fungal
import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as BH4Neural
import DASHI.Biology.BH4NOSCouplingEvidenceExact as BH4NOS
import DASHI.Culture.AmyEskridgeLiTorrMechanismBridgeExact as Eskridge
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact as Antigravity

------------------------------------------------------------------------
-- Source-owner projections: these are ALREADY paid by existing definitions.
-- New bridge is not a new empirical measurement or a replacement proof.
------------------------------------------------------------------------

canonicalFieldNeedsPerturbation :
  LevinField.FieldControlBoundary.causalFieldEffectRequiresPerturbation
    LevinField.canonicalFieldControlBoundary ≡ true
canonicalFieldNeedsPerturbation = refl

canonicalFieldCorrelationNotCausalProof :
  LevinField.FieldControlBoundary.correlationDoesNotEstablishCausalControl
    LevinField.canonicalFieldControlBoundary ≡ true
canonicalFieldCorrelationNotCausalProof = refl

sheldrakeQuestionAlreadyOwnedByLevin :
  Fungal.FungalCollectiveIntelligenceCore.sheldrakeStyleBoundaryQuestionsRemainScaleIndexed
    Fungal.canonicalFungalCollectiveIntelligenceCore ≡ true
sheldrakeQuestionAlreadyOwnedByLevin = refl

bh4CurrentTotalPoolNotSoleSufficientCause :
  BH4Neural.NeuralContextBoundary.simpleCurrentPoolSufficiencySupported
    BH4Neural.canonicalNeuralContextBoundary ≡ false
bh4CurrentTotalPoolNotSoleSufficientCause =
  BH4Neural.NeuralContextBoundary.simpleCurrentPoolSufficiencySupportedIsFalse
    BH4Neural.canonicalNeuralContextBoundary

bh4DevelopmentalHistoryMatters :
  BH4Neural.NeuralContextBoundary.developmentalTimingMatters
    BH4Neural.canonicalNeuralContextBoundary ≡ true
bh4DevelopmentalHistoryMatters =
  BH4Neural.NeuralContextBoundary.developmentalTimingMattersIsTrue
    BH4Neural.canonicalNeuralContextBoundary

nos3SourceEvidenceNotWholeAllocator :
  BH4NOS.NOS3EvidenceBoundary.couplingEvidencePaysWholeBH4Allocator
    BH4NOS.canonicalNOS3EvidenceBoundary ≡ false
nos3SourceEvidenceNotWholeAllocator =
  BH4NOS.NOS3EvidenceBoundary.couplingEvidencePaysWholeBH4AllocatorIsFalse
    BH4NOS.canonicalNOS3EvidenceBoundary

eskridgeLiTorrHistoryDoesNotEstablishEnhancement :
  Eskridge.EskridgeLiTorrPromotionBoundary.eskridgeDiscussionPlusLiTorrEquationsEstablishesEnhancement
    Eskridge.canonicalEskridgeLiTorrPromotionBoundary ≡ false
eskridgeLiTorrHistoryDoesNotEstablishEnhancement =
  Eskridge.EskridgeLiTorrPromotionBoundary.eskridgeDiscussionPlusLiTorrEquationsEstablishesEnhancementIsFalse
    Eskridge.canonicalEskridgeLiTorrPromotionBoundary

antigravityTypedCutDoesNotProveClaim :
  Antigravity.ClaimScopedCutBoundary.claimScopedCutAutomaticallyProvesClaim
    Antigravity.canonicalClaimScopedCutBoundary ≡ false
antigravityTypedCutDoesNotProveClaim = refl

unresolvedBoundaryChannelIsNotZero :
  Ledger.AdmittedChannelSet.unresolvedChannelsAreNotZero
    Ledger.canonicalAdmittedChannels ≡ true
unresolvedBoundaryChannelIsNotZero = refl

------------------------------------------------------------------------
-- Purely FINITE logical counterexample:
-- a stipulated equal input ledger does not uniquely identify the outcome
-- shape. This does NOT assert that a real magnetic field needs zero work,
-- that energy alone has four possible physical states, or that there is a
-- causally active extra "formal field".
------------------------------------------------------------------------

data OutcomeShape : Set where symmetric skewed : OutcomeShape

record AbstractShapeAndPaidWork : Set where
  constructor shape-and-work
  field
    outcomeShape : OutcomeShape
    paidUnits : Nat

referenceFiniteChart : AbstractShapeAndPaidWork
referenceFiniteChart = shape-and-work symmetric 4

biasedFiniteChart : AbstractShapeAndPaidWork
biasedFiniteChart = shape-and-work skewed 4

sameStipulatedBudget :
  AbstractShapeAndPaidWork.paidUnits referenceFiniteChart ≡
  AbstractShapeAndPaidWork.paidUnits biasedFiniteChart
sameStipulatedBudget = refl

data Impossible : Set where

differentOutcomesAtSameStipulatedBudget :
  AbstractShapeAndPaidWork.outcomeShape referenceFiniteChart ≡
  AbstractShapeAndPaidWork.outcomeShape biasedFiniteChart → Impossible
differentOutcomesAtSameStipulatedBudget ()

-- Distinguish the four senses in the original transcript without asserting
-- that physical field effects are "non-energetic" in modern physics.
data CauseQuestion : Set where
  matterCarrier efficientWork formalPattern finalTarget : CauseQuestion

record FourQuestionAudit : Set where
  constructor four-question-audit
  field
    matterSourceIdentity : Bool
    sameBoundaryWorkPaid : Bool
    patternChangeActuallyMeasured : Bool
    targetSpecifiedIndependentOfPattern : Bool

-- This is a *question inventory*, not a source-paid positive causal receipt.
unpaidAudit : FourQuestionAudit
unpaidAudit = four-question-audit false false false false
