module DASHI.Governance.IranThreatRepressionCaseNarrowingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.ExternalThreatRepressionMechanismTransferExact as Transfer

------------------------------------------------------------------------
-- IRAN 2026: CASE-SPECIFIC THREAT / REPRESSION NARROWING
--
-- Paid:
--   * general external-threat -> repression pathway exists
--   * Iran had pre-existing repression
--   * strike exposure shifted mobilisation composition
--   * current external-threat conditions coexist with intensified domestic
--     controls / crackdown reporting
--
-- Unpaid:
--   * identification of the marginal repression increment caused by the
--     external threat, net of pre-existing regime-security dynamics.
------------------------------------------------------------------------

reutersOct1 : Source.AttributedSource
reutersOct1 = Source.mkNoDOISource
  "Reuters"
  "Iran readies harder retaliation if attacked as diplomacy faces long odds"
  "Reuters"
  "2026-10-01"
  "https://www.reuters.com/world/middle-east/iran-readies-harder-retaliation-if-attacked-diplomacy-faces-long-odds-2026-10-01/"
  Source.newsSource
  "current report linking continuing external military risk, concern over renewed internal unrest, and intensified domestic controls; current reporting only, not a causal experiment"
  Source.publicAttribution

record CaseNarrowingReceipt : Set where
  constructor case-narrowing-receipt
  field
    generalTransfer : Transfer.CaseTransferReceipt
    currentSource : Source.AttributedSource
    preExistingRepressionRetained : Bool
    preExistingRepressionRetainedIsTrue :
      preExistingRepressionRetained ≡ true
    externalThreatSurfacePaid : Bool
    externalThreatSurfacePaidIsTrue :
      externalThreatSurfacePaid ≡ true
    intensifiedControlSurfacePaid : Bool
    intensifiedControlSurfacePaidIsTrue :
      intensifiedControlSurfacePaid ≡ true
    mobilisationShiftPaid : Bool
    mobilisationShiftPaidIsTrue :
      mobilisationShiftPaid ≡ true
    marginalRepressionIncrementIdentified : Bool
    marginalRepressionIncrementIdentifiedIsFalse :
      marginalRepressionIncrementIdentified ≡ false
    externalThreatNecessaryForRepression : Bool
    externalThreatNecessaryForRepressionIsFalse :
      externalThreatNecessaryForRepression ≡ false

open CaseNarrowingReceipt public

canonicalIranCaseNarrowing : CaseNarrowingReceipt
canonicalIranCaseNarrowing =
  case-narrowing-receipt
    Transfer.iran2026Transfer
    reutersOct1
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

record SameEpisodeResidual : Set where
  constructor same-episode-residual
  field
    residualRef : String
    requiredObject : String
    identificationTarget : String
    retainedCounterHypotheses : String
    mayPromoteGeneralMechanismToCase : Bool
    mayPromoteGeneralMechanismToCaseIsFalse :
      mayPromoteGeneralMechanismToCase ≡ false

open SameEpisodeResidual public

sameEpisodeResidual : SameEpisodeResidual
sameEpisodeResidual =
  same-episode-residual
    "residual:iran-2026:marginal-repression-increment"
    "same-episode policy/order/timing record, subnational exposure design, or other Iran-specific evidence identifying repression change after external-threat exposure"
    "marginal repression attributable to external threat, not total observed repression"
    "pre-existing coercive institutions; protest intensity; economic crisis; regime-security incentives; foreign-agent framing; state-capacity adaptation"
    false refl

data CoOccurrenceMeansMarginalCausation : Set where
data IntensifiedControlReportingMeansThreatNecessity : Set where
data GeneralCausalPriorClosesCase : Set where

coOccurrenceDoesNotIdentifyMarginalCausation :
  CoOccurrenceMeansMarginalCausation → ⊥
coOccurrenceDoesNotIdentifyMarginalCausation ()

controlReportingDoesNotCreateNecessity :
  IntensifiedControlReportingMeansThreatNecessity → ⊥
controlReportingDoesNotCreateNecessity ()

generalPriorDoesNotCloseIranCase :
  GeneralCausalPriorClosesCase → ⊥
generalPriorDoesNotCloseIranCase ()

reutersSnowball :
  Snowball.SourceRoleSnowballReceipt reutersOct1
reutersSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt reutersOct1
