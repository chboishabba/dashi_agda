module DASHI.Culture.MissingDeceasedCommonProgrammePromotionStateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common
import DASHI.Culture.MissingDeceasedLiteralObjectEvidenceLadderExact as Ladder
import DASHI.Culture.MissingDeceasedLiteralCrossPersonIdentifierSearchExact as Search

------------------------------------------------------------------------
-- CURRENT HYPOTHESIS PROMOTION STATE
--
-- Literal programme/object identifiers increase acquisition precision, not the
-- hypothesis level. H2 requires a literal cross-person same-programme receipt;
-- H3 additionally requires pre-event operational evidence.
------------------------------------------------------------------------

record PromotionState : Set where
  constructor promotion-state
  field
    hypothesis : Common.HypothesisClass
    literalProgrammeObjectIdentifiers : Nat
    literalPersonReferences : Nat
    literalCrossPersonSameProgrammeReceipts : Nat
    preEventOperationalReceipts : Nat
    h0StillAdmissible : Bool
    h2Paid : Bool
    h3Paid : Bool
    nextPromotionCondition : String

open PromotionState public

currentPromotionState : PromotionState
currentPromotionState = promotion-state
  Common.H1
  Ladder.literalProgrammeObjectIdentifierCount
  Ladder.literalPersonReferenceCount
  Ladder.literalCrossPersonSameProgrammeCount
  Ladder.preEventOperationalLinkCount
  true false false
  "H2 requires one source-backed pre-event same-programme/work-package/apparatus receipt spanning at least two retained people; H3 additionally requires operational targeting/security/action evidence"

currentHypothesis : Common.HypothesisClass
currentHypothesis = Common.H1

h0Admissible : Bool
h0Admissible = true

h1BestPaidCurrentBroadModel : Bool
h1BestPaidCurrentBroadModel = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

programmeObjectIdsIncreaseSearchPriority : Bool
programmeObjectIdsIncreaseSearchPriority = true

programmeObjectIdsIncreaseHypothesisLevel : Bool
programmeObjectIdsIncreaseHypothesisLevel = false

explicitHistoricalReferenceIncreasesSearchPriority : Bool
explicitHistoricalReferenceIncreasesSearchPriority = true

explicitHistoricalReferencePaysSharedProgramme : Bool
explicitHistoricalReferencePaysSharedProgramme = false

postEventGovernmentAggregationPaysPreEventOperationalLink : Bool
postEventGovernmentAggregationPaysPreEventOperationalLink = false

laterProgrammePersistencePaysEarlierPersonInvolvement : Bool
laterProgrammePersistencePaysEarlierPersonInvolvement = false

searchResidualProvesNoCommonProgramme : Bool
searchResidualProvesNoCommonProgramme = false

literalIdentifierSearchStateRetained : Bool
literalIdentifierSearchStateRetained = true

------------------------------------------------------------------------
-- Current exact promotion gates, exposed for downstream schedulers.
------------------------------------------------------------------------

h2NeededCrossPersonSameProgrammeReceipts : Nat
h2NeededCrossPersonSameProgrammeReceipts = 1

h3NeededPreEventOperationalReceipts : Nat
h3NeededPreEventOperationalReceipts = 1

currentH2CrossPersonDeficit : Nat
currentH2CrossPersonDeficit = 1

currentH3OperationalDeficit : Nat
currentH3OperationalDeficit = 1

nextHighestAlphaPromotionSearch : String
nextHighestAlphaPromotionSearch =
  "first: inspect DAAH01-01-9-R001 SOW/closeout and pre-2013 AFRL Mondaloy programme records for a second retained person; second: inspect Amy NASA/Institute release object for AC Gravity/Army identifier reuse; third: search exact NUDT/JPL work-package IDs"
