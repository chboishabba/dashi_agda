module DASHI.Culture.AmyEskridgeVideoTypedObligationWeldExact where

-- DASHI-native typed obligations for EVERY claim in the user-supplied
-- "She Researched Something THEY DON'T ALLOW. Then She Died" transcript.
-- All claim content and source identity remain owned by the separately
-- imported 86-row welded attribution ledger.
-- Source policy: Docs/SourceAttributionPolicy.md.
-- Primary sources: HAL5 Amy Eskridge 2018; House Oversight 2026-04-20;
-- source-specific DOI/patent objects in AmyEskridgeVideoClaimProducerWeldExact.
-- Typed obligations are our research criteria, not the speakers' claims.
-- The late-video clip lineage (claims 064–085) has its own source-typed
-- BIDI; exact historical-quotation source identification is no longer an
-- outstanding experiment/operation receipt. Claim070's original voice is
-- still unresolved, while psychology vs pre-stimulus physiology remains
-- separated by the existing temporal evidence fibre.
-- Original Zoom clip provenance is now supplied for claim001-003,
-- claim005-007 and claim010, and secondary Fox media list is identified
-- for claim004. Those source-identity gates have been narrowed here;
-- independent event/physics/causality gates remain OPEN.
-- Explicit lack of a constructor for these receipts records an OPEN leaf;
-- it does not mean the underlying event has been disproved.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Culture.AmyEskridgeVideoClaimProducerWeldExact as Weld

data RequiredReceipt : Set where
  sourceClipProvenance : RequiredReceipt
  independentRecordingIntegrity : RequiredReceipt
  rosterIdentity : RequiredReceipt
  denominatorAndControls : RequiredReceipt
  commonProgrammeLink : RequiredReceipt
  independentEventFile : RequiredReceipt
  causalSequence : RequiredReceipt
  originalExperimentData : RequiredReceipt
  controlledReplication : RequiredReceipt
  physicalApparatus : RequiredReceipt
  independentlyObservableEffect : RequiredReceipt
  primaryFullText : RequiredReceipt
  technicalConclusionScope : RequiredReceipt
  officialProgrammeObject : RequiredReceipt
  operationalOutcome : RequiredReceipt
  fullEnergyAndCostAccounting : RequiredReceipt
  claimClipContext : RequiredReceipt

record TypedClaimGate : Set where
  constructor typed-claim-gate
  field
    sourceWeld : Weld.VideoClaimJoin
    outstandingReceiptTypes : List RequiredReceipt
    noAutomaticPromotion : String

open TypedClaimGate public

gate001 : TypedClaimGate
gate001 = typed-claim-gate Weld.claimJoin001
  (independentRecordingIntegrity ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate002 : TypedClaimGate
gate002 = typed-claim-gate Weld.claimJoin002
  (officialProgrammeObject ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate003 : TypedClaimGate
gate003 = typed-claim-gate Weld.claimJoin003
  (originalExperimentData ∷ causalSequence ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate004 : TypedClaimGate
gate004 = typed-claim-gate Weld.claimJoin004
  (sourceClipProvenance ∷ denominatorAndControls ∷ commonProgrammeLink ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate005 : TypedClaimGate
gate005 = typed-claim-gate Weld.claimJoin005
  (independentRecordingIntegrity ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate006 : TypedClaimGate
gate006 = typed-claim-gate Weld.claimJoin006
  (independentRecordingIntegrity ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate007 : TypedClaimGate
gate007 = typed-claim-gate Weld.claimJoin007
  (independentRecordingIntegrity ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate008 : TypedClaimGate
gate008 = typed-claim-gate Weld.claimJoin008
  (rosterIdentity ∷ denominatorAndControls ∷ commonProgrammeLink ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate009 : TypedClaimGate
gate009 = typed-claim-gate Weld.claimJoin009
  (independentEventFile ∷ causalSequence ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate010 : TypedClaimGate
gate010 = typed-claim-gate Weld.claimJoin010
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate011 : TypedClaimGate
gate011 = typed-claim-gate Weld.claimJoin011
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate012 : TypedClaimGate
gate012 = typed-claim-gate Weld.claimJoin012
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate013 : TypedClaimGate
gate013 = typed-claim-gate Weld.claimJoin013
  (primaryFullText ∷ claimClipContext ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate014 : TypedClaimGate
gate014 = typed-claim-gate Weld.claimJoin014
  (fullEnergyAndCostAccounting ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate015 : TypedClaimGate
gate015 = typed-claim-gate Weld.claimJoin015
  (primaryFullText ∷ claimClipContext ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate016 : TypedClaimGate
gate016 = typed-claim-gate Weld.claimJoin016
  (rosterIdentity ∷ denominatorAndControls ∷ commonProgrammeLink ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate017 : TypedClaimGate
gate017 = typed-claim-gate Weld.claimJoin017
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate018 : TypedClaimGate
gate018 = typed-claim-gate Weld.claimJoin018
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate019 : TypedClaimGate
gate019 = typed-claim-gate Weld.claimJoin019
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate020 : TypedClaimGate
gate020 = typed-claim-gate Weld.claimJoin020
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate021 : TypedClaimGate
gate021 = typed-claim-gate Weld.claimJoin021
  (fullEnergyAndCostAccounting ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate022 : TypedClaimGate
gate022 = typed-claim-gate Weld.claimJoin022
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate023 : TypedClaimGate
gate023 = typed-claim-gate Weld.claimJoin023
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate024 : TypedClaimGate
gate024 = typed-claim-gate Weld.claimJoin024
  (causalSequence ∷ denominatorAndControls ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate025 : TypedClaimGate
gate025 = typed-claim-gate Weld.claimJoin025
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate026 : TypedClaimGate
gate026 = typed-claim-gate Weld.claimJoin026
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate027 : TypedClaimGate
gate027 = typed-claim-gate Weld.claimJoin027
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate028 : TypedClaimGate
gate028 = typed-claim-gate Weld.claimJoin028
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate029 : TypedClaimGate
gate029 = typed-claim-gate Weld.claimJoin029
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate030 : TypedClaimGate
gate030 = typed-claim-gate Weld.claimJoin030
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate031 : TypedClaimGate
gate031 = typed-claim-gate Weld.claimJoin031
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate032 : TypedClaimGate
gate032 = typed-claim-gate Weld.claimJoin032
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate033 : TypedClaimGate
gate033 = typed-claim-gate Weld.claimJoin033
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate034 : TypedClaimGate
gate034 = typed-claim-gate Weld.claimJoin034
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate035 : TypedClaimGate
gate035 = typed-claim-gate Weld.claimJoin035
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate036 : TypedClaimGate
gate036 = typed-claim-gate Weld.claimJoin036
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate037 : TypedClaimGate
gate037 = typed-claim-gate Weld.claimJoin037
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate038 : TypedClaimGate
gate038 = typed-claim-gate Weld.claimJoin038
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate039 : TypedClaimGate
gate039 = typed-claim-gate Weld.claimJoin039
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate040 : TypedClaimGate
gate040 = typed-claim-gate Weld.claimJoin040
  (rosterIdentity ∷ denominatorAndControls ∷ commonProgrammeLink ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate041 : TypedClaimGate
gate041 = typed-claim-gate Weld.claimJoin041
  (independentEventFile ∷ causalSequence ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate042 : TypedClaimGate
gate042 = typed-claim-gate Weld.claimJoin042
  (independentEventFile ∷ causalSequence ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate043 : TypedClaimGate
gate043 = typed-claim-gate Weld.claimJoin043
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate044 : TypedClaimGate
gate044 = typed-claim-gate Weld.claimJoin044
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate045 : TypedClaimGate
gate045 = typed-claim-gate Weld.claimJoin045
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate046 : TypedClaimGate
gate046 = typed-claim-gate Weld.claimJoin046
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate047 : TypedClaimGate
gate047 = typed-claim-gate Weld.claimJoin047
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate048 : TypedClaimGate
gate048 = typed-claim-gate Weld.claimJoin048
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate049 : TypedClaimGate
gate049 = typed-claim-gate Weld.claimJoin049
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate050 : TypedClaimGate
gate050 = typed-claim-gate Weld.claimJoin050
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate051 : TypedClaimGate
gate051 = typed-claim-gate Weld.claimJoin051
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate052 : TypedClaimGate
gate052 = typed-claim-gate Weld.claimJoin052
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate053 : TypedClaimGate
gate053 = typed-claim-gate Weld.claimJoin053
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate054 : TypedClaimGate
gate054 = typed-claim-gate Weld.claimJoin054
  (officialProgrammeObject ∷ operationalOutcome ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate055 : TypedClaimGate
gate055 = typed-claim-gate Weld.claimJoin055
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate056 : TypedClaimGate
gate056 = typed-claim-gate Weld.claimJoin056
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate057 : TypedClaimGate
gate057 = typed-claim-gate Weld.claimJoin057
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate058 : TypedClaimGate
gate058 = typed-claim-gate Weld.claimJoin058
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate059 : TypedClaimGate
gate059 = typed-claim-gate Weld.claimJoin059
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate060 : TypedClaimGate
gate060 = typed-claim-gate Weld.claimJoin060
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate061 : TypedClaimGate
gate061 = typed-claim-gate Weld.claimJoin061
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate062 : TypedClaimGate
gate062 = typed-claim-gate Weld.claimJoin062
  (primaryFullText ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate063 : TypedClaimGate
gate063 = typed-claim-gate Weld.claimJoin063
  (rosterIdentity ∷ denominatorAndControls ∷ commonProgrammeLink ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate064 : TypedClaimGate
gate064 = typed-claim-gate Weld.claimJoin064
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate065 : TypedClaimGate
gate065 = typed-claim-gate Weld.claimJoin065
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate066 : TypedClaimGate
gate066 = typed-claim-gate Weld.claimJoin066
  (claimClipContext ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate067 : TypedClaimGate
gate067 = typed-claim-gate Weld.claimJoin067
  (claimClipContext ∷ technicalConclusionScope ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate068 : TypedClaimGate
gate068 = typed-claim-gate Weld.claimJoin068
  (denominatorAndControls ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate069 : TypedClaimGate
gate069 = typed-claim-gate Weld.claimJoin069
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate070 : TypedClaimGate
gate070 = typed-claim-gate Weld.claimJoin070
  (sourceClipProvenance ∷ independentRecordingIntegrity ∷ originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate071 : TypedClaimGate
gate071 = typed-claim-gate Weld.claimJoin071
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate072 : TypedClaimGate
gate072 = typed-claim-gate Weld.claimJoin072
  (originalExperimentData ∷ controlledReplication ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate073 : TypedClaimGate
gate073 = typed-claim-gate Weld.claimJoin073
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate074 : TypedClaimGate
gate074 = typed-claim-gate Weld.claimJoin074
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate075 : TypedClaimGate
gate075 = typed-claim-gate Weld.claimJoin075
  (originalExperimentData ∷ controlledReplication ∷ claimClipContext ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate076 : TypedClaimGate
gate076 = typed-claim-gate Weld.claimJoin076
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate077 : TypedClaimGate
gate077 = typed-claim-gate Weld.claimJoin077
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate078 : TypedClaimGate
gate078 = typed-claim-gate Weld.claimJoin078
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate079 : TypedClaimGate
gate079 = typed-claim-gate Weld.claimJoin079
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate080 : TypedClaimGate
gate080 = typed-claim-gate Weld.claimJoin080
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate081 : TypedClaimGate
gate081 = typed-claim-gate Weld.claimJoin081
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate082 : TypedClaimGate
gate082 = typed-claim-gate Weld.claimJoin082
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate083 : TypedClaimGate
gate083 = typed-claim-gate Weld.claimJoin083
  (physicalApparatus ∷ independentlyObservableEffect ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate084 : TypedClaimGate
gate084 = typed-claim-gate Weld.claimJoin084
  (independentEventFile ∷ causalSequence ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate085 : TypedClaimGate
gate085 = typed-claim-gate Weld.claimJoin085
  (officialProgrammeObject ∷ independentEventFile ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

gate086 : TypedClaimGate
gate086 = typed-claim-gate Weld.claimJoin086
  (causalSequence ∷ denominatorAndControls ∷ [])
  "Unpaid independent witness; citation identity and transcript statement are not promotion permissions"

allVideoGates : List TypedClaimGate
allVideoGates =
  gate001 ∷
  gate002 ∷
  gate003 ∷
  gate004 ∷
  gate005 ∷
  gate006 ∷
  gate007 ∷
  gate008 ∷
  gate009 ∷
  gate010 ∷
  gate011 ∷
  gate012 ∷
  gate013 ∷
  gate014 ∷
  gate015 ∷
  gate016 ∷
  gate017 ∷
  gate018 ∷
  gate019 ∷
  gate020 ∷
  gate021 ∷
  gate022 ∷
  gate023 ∷
  gate024 ∷
  gate025 ∷
  gate026 ∷
  gate027 ∷
  gate028 ∷
  gate029 ∷
  gate030 ∷
  gate031 ∷
  gate032 ∷
  gate033 ∷
  gate034 ∷
  gate035 ∷
  gate036 ∷
  gate037 ∷
  gate038 ∷
  gate039 ∷
  gate040 ∷
  gate041 ∷
  gate042 ∷
  gate043 ∷
  gate044 ∷
  gate045 ∷
  gate046 ∷
  gate047 ∷
  gate048 ∷
  gate049 ∷
  gate050 ∷
  gate051 ∷
  gate052 ∷
  gate053 ∷
  gate054 ∷
  gate055 ∷
  gate056 ∷
  gate057 ∷
  gate058 ∷
  gate059 ∷
  gate060 ∷
  gate061 ∷
  gate062 ∷
  gate063 ∷
  gate064 ∷
  gate065 ∷
  gate066 ∷
  gate067 ∷
  gate068 ∷
  gate069 ∷
  gate070 ∷
  gate071 ∷
  gate072 ∷
  gate073 ∷
  gate074 ∷
  gate075 ∷
  gate076 ∷
  gate077 ∷
  gate078 ∷
  gate079 ∷
  gate080 ∷
  gate081 ∷
  gate082 ∷
  gate083 ∷
  gate084 ∷
  gate085 ∷
  gate086 ∷ []

forgetOpenGates : List TypedClaimGate → List Weld.VideoClaimJoin
forgetOpenGates [] = []
forgetOpenGates (x ∷ xs) = sourceWeld x ∷ forgetOpenGates xs

-- All 86 source welds have one matching typed remaining-gate packet.
gateCoverage : forgetOpenGates allVideoGates ≡ Weld.allVideoClaimJoins
gateCoverage = refl

-- These are uninhabited *current evidence promotions*, not assertions of
-- empirical impossibility; a future gate needs a newly
-- source-attributed proof-owning producer and a reviewed migration.
data AutomaticallyClosedFromTranscript : Set where
data AutomaticallyClosedFromMentionedDOI : Set where
data AutomaticallyClosedFromHouseConcern : Set where
