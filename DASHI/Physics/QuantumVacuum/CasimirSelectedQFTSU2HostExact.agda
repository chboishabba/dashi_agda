module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsCompactSimpleGroupPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Physics.Closure.YMSprint105CompactSimpleGroupParameterTable as Table

------------------------------------------------------------------------
-- SELECTED-QFT SU(2) HOST
--
-- The compatibility host below still exposes the historical all-group
-- interpretation function.  The physical max-cut no longer charges that whole
-- function: downstream Casimir/U(1) consumers use only the selected group.
--
-- A proof-relevant SelectedGroupStructureRealization therefore carries exactly
-- the load-bearing statement: one concrete GroupStructure really is the
-- structure of THIS selected compact-simple index, and that same structure is
-- the repository's unit-quaternion SU(2).  A bare quaternionic group law is not
-- by itself such an identification.
------------------------------------------------------------------------

record CasimirSelectedQFTSU2Host
    (U : Weld.UnifiedCandidate)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    selectedGroupIsCompactSimple :
      QFT.IsCompactSimple (Weld.qftSemantics U) group

    groupStructureInterpretation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure

    selectedGroupStructureIsQuaternionSU2 :
      groupStructureInterpretation group ≡ SU2.su2QuaternionGroup

    reading : String

open CasimirSelectedQFTSU2Host public

record SelectedGroupStructureRealization
    (U : Weld.UnifiedCandidate)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    realizedGroupStructure : Gauge.GroupStructure

    SameSelectedGroupStructure : Set
    sameSelectedGroupStructure : SameSelectedGroupStructure

    realizedStructureIsQuaternionSU2 :
      realizedGroupStructure ≡ SU2.su2QuaternionGroup

    realizationReading : String

open SelectedGroupStructureRealization public

-- Optional classification receipt.  This is deliberately downstream of the
-- literal host because the selected-structure equality already suffices for U(1).
record CasimirSelectedQFTSU2DynkinConsistency
    {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)}
    (host : CasimirSelectedQFTSU2Host U group) : Set₁ where
  field
    compactSimpleDataForGroup :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Promotion.CompactSimpleYMData
        (QFT.CompactSimpleGroup (Weld.qftCarriers U))

    selectedGroupDynkinFamilyIsA1 :
      Promotion.family (compactSimpleDataForGroup group)
      ≡ Promotion.familyA 1

open CasimirSelectedQFTSU2DynkinConsistency public

------------------------------------------------------------------------
-- Existing same-object routes that already own compact simplicity.
------------------------------------------------------------------------

compactSimpleFromPinnedYMConstruction :
  ∀ {U : Weld.UnifiedCandidate} →
  (pinned :
    Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U}
      (Weld.qftSemantics U)) →
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  QFT.IsCompactSimple (Weld.qftSemantics U) group
compactSimpleFromPinnedYMConstruction pinned group =
  Pinned.compactSimple pinned group

compactSimpleFromLiteralClayStructuralBase :
  ∀ {U : Weld.UnifiedCandidate}
    (candidate : Weld.Candidate U) →
  Five.LiteralClayStructuralBase (Weld.qftTarget U candidate) →
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  QFT.IsCompactSimple (Weld.qftSemantics U) group
compactSimpleFromLiteralClayStructuralBase candidate structural group =
  Five.compactSimple structural group

------------------------------------------------------------------------
-- Selected-only compilers.  The constant compatibility interpretation exists
-- solely to inhabit the legacy host shape; its physical authority comes from
-- the indexed SelectedGroupStructureRealization payment, not from constancy.
------------------------------------------------------------------------

hostFromPinnedSelectedStructure :
  ∀ {U : Weld.UnifiedCandidate}
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  SelectedGroupStructureRealization U group →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromPinnedSelectedStructure pinned group realization reading = record
  { selectedGroupIsCompactSimple =
      compactSimpleFromPinnedYMConstruction pinned group
  ; groupStructureInterpretation =
      λ _ → realizedGroupStructure realization
  ; selectedGroupStructureIsQuaternionSU2 =
      realizedStructureIsQuaternionSU2 realization
  ; reading = reading
  }

hostFromStructuralBaseSelectedStructure :
  ∀ {U : Weld.UnifiedCandidate}
    (candidate : Weld.Candidate U)
    (structural : Five.LiteralClayStructuralBase (Weld.qftTarget U candidate))
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  SelectedGroupStructureRealization U group →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromStructuralBaseSelectedStructure
    candidate structural group realization reading = record
  { selectedGroupIsCompactSimple =
      compactSimpleFromLiteralClayStructuralBase candidate structural group
  ; groupStructureInterpretation =
      λ _ → realizedGroupStructure realization
  ; selectedGroupStructureIsQuaternionSU2 =
      realizedStructureIsQuaternionSU2 realization
  ; reading = reading
  }

------------------------------------------------------------------------
-- Compatibility constructors retained for existing callers.  They do not
-- replace the selected-index same-object realization in the current max-cut.
------------------------------------------------------------------------

hostFromPinnedYMConstruction :
  ∀ {U : Weld.UnifiedCandidate}
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (interpretation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure) →
  interpretation group ≡ SU2.su2QuaternionGroup →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromPinnedYMConstruction
    pinned group interpretation interpreted reading = record
  { selectedGroupIsCompactSimple = compactSimpleFromPinnedYMConstruction pinned group
  ; groupStructureInterpretation = interpretation
  ; selectedGroupStructureIsQuaternionSU2 = interpreted
  ; reading = reading
  }

hostFromLiteralClayStructuralBase :
  ∀ {U : Weld.UnifiedCandidate}
    (candidate : Weld.Candidate U)
    (structural : Five.LiteralClayStructuralBase (Weld.qftTarget U candidate))
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (interpretation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure) →
  interpretation group ≡ SU2.su2QuaternionGroup →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromLiteralClayStructuralBase
    candidate structural group interpretation interpreted reading = record
  { selectedGroupIsCompactSimple =
      compactSimpleFromLiteralClayStructuralBase candidate structural group
  ; groupStructureInterpretation = interpretation
  ; selectedGroupStructureIsQuaternionSU2 = interpreted
  ; reading = reading
  }

selectedGroupCarrierIsQuaternionSU2 :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)} →
  (host : CasimirSelectedQFTSU2Host U group) →
  Gauge.Carrier (groupStructureInterpretation host group) ≡ SU2.SU2Quaternion
selectedGroupCarrierIsQuaternionSU2 host =
  cong Gauge.Carrier (selectedGroupStructureIsQuaternionSU2 host)

u1InclusionIntoSelectedQFTGroupCarrier :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)} →
  (host : CasimirSelectedQFTSU2Host U group) →
  U1.U1TorusElement →
  Gauge.Carrier (groupStructureInterpretation host group)
u1InclusionIntoSelectedQFTGroupCarrier host u =
  subst
    (λ CarrierType → CarrierType)
    (sym (selectedGroupCarrierIsQuaternionSU2 host))
    (U1.includeU1InSU2 u)

selectedQFTGroupHasLiteralU1InclusionAfterHost : Bool
selectedQFTGroupHasLiteralU1InclusionAfterHost = true

concreteQuaternionSU2Group : Gauge.GroupStructure
concreteQuaternionSU2Group = SU2.su2QuaternionGroup

canonicalSU2ParameterEntry : Table.CompactSimpleGroupEntry
canonicalSU2ParameterEntry = Table.SU2

canonicalSU2ParameterRow : Table.GroupParameterRow
canonicalSU2ParameterRow = Table.su2ParameterRow

data Sprint105SU2EntryAutomaticallyIdentifiesUnifiedCandidateGroup : Set where
data QuaternionSU2AutomaticallyChoosesUnifiedCandidateGroup : Set where
data BareQuaternionStructureAutomaticallyRealizesSelectedGroup : Set where
data SelectedSU2HostAutomaticallyIdentifiesBrownMaclayStress : Set where

tableEntryDoesNotChooseCandidateGroup :
  Sprint105SU2EntryAutomaticallyIdentifiesUnifiedCandidateGroup → ⊥
tableEntryDoesNotChooseCandidateGroup ()

quaternionSU2DoesNotChooseCandidateGroup :
  QuaternionSU2AutomaticallyChoosesUnifiedCandidateGroup → ⊥
quaternionSU2DoesNotChooseCandidateGroup ()

bareQuaternionStructureDoesNotRealizeSelectedGroup :
  BareQuaternionStructureAutomaticallyRealizesSelectedGroup → ⊥
bareQuaternionStructureDoesNotRealizeSelectedGroup ()

selectedSU2HostDoesNotIdentifyBrownMaclayStress :
  SelectedSU2HostAutomaticallyIdentifiesBrownMaclayStress → ⊥
selectedSU2HostDoesNotIdentifyBrownMaclayStress ()

record CasimirSelectedQFTSU2HostBoundary : Set where
  constructor casimir-selected-qft-su2-host-boundary
  field
    concreteQuaternionSU2GroupOwned : Bool
    sprint105SU2EntryOwned : Bool
    compactSimpleYMDataInterfaceReused : Bool
    selectedQFTSU2HostInterfaceOwned : Bool
    selectedGroupStructureRealizationInterfaceOwned : Bool
    allGroupsStructureInterpretationRequiredForHost : Bool
    selectedStructureRealizationBuildsHostCompilerOwned : Bool
    literalU1InclusionCompilerOwnedAfterHost : Bool
    pinnedYMConstructionSuppliesCompactSimpleCompiler : Bool
    literalClayStructuralBaseSuppliesCompactSimpleCompiler : Bool
    sprint105ClassificationIsSecondaryConsistencyTag : Bool
    sprint105ClassificationRequiredForHost : Bool
    dynkinA1ClassificationRequiredForHost : Bool

    selectedGroupCompactSimpleWitnessPaid : Bool
    selectedGroupDynkinA1ClassificationPaid : Bool
    selectedGroupInterpretedAsQuaternionSU2Paid : Bool
    brownMaclayStressIdentifiedByHostAlone : Bool

open CasimirSelectedQFTSU2HostBoundary public

canonicalCasimirSelectedQFTSU2HostBoundary :
  CasimirSelectedQFTSU2HostBoundary
canonicalCasimirSelectedQFTSU2HostBoundary =
  casimir-selected-qft-su2-host-boundary
    true true true true true false true true true true true false false
    false false false false

casimirSelectedQFTSU2HostReading : String
casimirSelectedQFTSU2HostReading =
  "The current selected-QFT host no longer charges an arbitrary all-compact-simple-group interpretation function as physical input. A SelectedGroupStructureRealization indexed by the chosen compact-simple token carries the genuine same-object payment that one GroupStructure realizes THIS selected group and that the same structure is the existing unit-quaternion SU(2). That indexed realization plus existing compact-simplicity evidence compiles the compatibility host and literal U(1) inclusion. A bare quaternionic group law, Sprint105 SU2 row, or Dynkin-A1 label does not identify the selected group. Brown-Maclay stress remains separate."
