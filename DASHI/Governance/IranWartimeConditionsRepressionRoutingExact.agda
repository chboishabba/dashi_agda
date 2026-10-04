module DASHI.Governance.IranWartimeConditionsRepressionRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IranThreatRepressionCaseNarrowingExact as Narrowing

------------------------------------------------------------------------
-- IRAN 2026: WARTIME-CONDITIONS -> REPRESSION ROUTING
--
-- Bounded result:
--   a human-rights investigation explicitly attributes an intensification of
--   internal repression to authorities' use of wartime conditions as cover.
--
-- This pays a qualitative routing mechanism.
-- It does NOT identify the marginal effect size, prove necessity, or show that
-- all repression observed in 2026 was caused by the external war.
------------------------------------------------------------------------

amnestyDualRisk2026 : Source.AttributedSource
amnestyDualRisk2026 = Source.mkNoDOISource
  "Amnesty International"
  "Iran: Trapped between unlawful attacks by the USA/Israel and internal deadly repression: People in Iran face dual atrocity risks"
  "Amnesty International Research Briefing"
  "2026-04-28"
  "https://www.amnesty.org/en/documents/mde13/0883/2026/en/"
  (Source.namedSourceKind "human-rights investigation / research briefing")
  "investigative source documenting both external attack harms and domestic repression; later Amnesty material explicitly states authorities used the cover of wartime conditions to intensify repression"
  Source.publicAttribution

amnestySept2026 : Source.AttributedSource
amnestySept2026 = Source.mkNoDOISource
  "Amnesty International"
  "Why is Amnesty International calling for international justice for crimes against humanity in Iran?"
  "Amnesty International"
  "2026-09"
  "https://www.amnesty.org/en/latest/campaigns/2026/09/why-is-amnesty-international-calling-for-international-justice-for-crimes-against-humanity-in-iran/"
  (Source.namedSourceKind "human-rights investigation / campaign explainer")
  "source explicitly attributes intensified internal repression, militarisation of public space, threats and politically motivated executions to authorities' use of wartime conditions as cover"
  Source.publicAttribution

record WartimeRoutingReceipt : Set where
  constructor wartime-routing-receipt
  field
    source : Source.AttributedSource
    externalThreatPresent : Bool
    externalThreatPresentIsTrue :
      externalThreatPresent ≡ true
    preExistingRepressionRetained : Bool
    preExistingRepressionRetainedIsTrue :
      preExistingRepressionRetained ≡ true
    wartimeConditionsUsedAsCover : Bool
    wartimeConditionsUsedAsCoverIsTrue :
      wartimeConditionsUsedAsCover ≡ true
    intensifiedRepressionAttributed : Bool
    intensifiedRepressionAttributedIsTrue :
      intensifiedRepressionAttributed ≡ true
    marginalEffectSizeIdentified : Bool
    marginalEffectSizeIdentifiedIsFalse :
      marginalEffectSizeIdentified ≡ false
    externalThreatNecessaryForRepression : Bool
    externalThreatNecessaryForRepressionIsFalse :
      externalThreatNecessaryForRepression ≡ false
    allObservedRepressionCausedByWar : Bool
    allObservedRepressionCausedByWarIsFalse :
      allObservedRepressionCausedByWar ≡ false

open WartimeRoutingReceipt public

canonicalWartimeRouting : WartimeRoutingReceipt
canonicalWartimeRouting =
  wartime-routing-receipt
    amnestySept2026
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

record ResidualSplit : Set where
  constructor residual-split
  field
    qualitativeRoutingPaid : Bool
    qualitativeRoutingPaidIsTrue :
      qualitativeRoutingPaid ≡ true
    quantitativeIncrementPaid : Bool
    quantitativeIncrementPaidIsFalse :
      quantitativeIncrementPaid ≡ false
    survivingResidual : Narrowing.SameEpisodeResidual

open ResidualSplit public

canonicalResidualSplit : ResidualSplit
canonicalResidualSplit =
  residual-split
    true refl
    false refl
    Narrowing.sameEpisodeResidual

data InvestigativeAttributionEqualsExperimentalEffectSize : Set where
data WartimeCoverMeansWarCreatedRepression : Set where
data IntensificationMeansAllRepressionIsNew : Set where

investigativeAttributionDoesNotCreateEffectSize :
  InvestigativeAttributionEqualsExperimentalEffectSize → ⊥
investigativeAttributionDoesNotCreateEffectSize ()

wartimeCoverDoesNotMeanWarCreatedRepression :
  WartimeCoverMeansWarCreatedRepression → ⊥
wartimeCoverDoesNotMeanWarCreatedRepression ()

intensificationDoesNotMakeAllRepressionNew :
  IntensificationMeansAllRepressionIsNew → ⊥
intensificationDoesNotMakeAllRepressionNew ()

amnestySnowball :
  Snowball.SourceRoleSnowballReceipt amnestySept2026
amnestySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt amnestySept2026
