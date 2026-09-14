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
