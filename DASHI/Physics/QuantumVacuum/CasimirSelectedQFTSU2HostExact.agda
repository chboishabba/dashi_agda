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
-- For the Casimir U(1) handoff, the load-bearing group statement is literal:
-- the selected compact-simple group is interpreted as the existing concrete
-- unit-quaternion SU(2) GroupStructure.  Dynkin-A1 / Sprint105 classification
-- is useful consistency metadata, but is not required to transport the
-- already-proved U(1) torus inclusion into the selected carrier.
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

-- Optional classification receipt.  This is deliberately downstream of the
-- literal host because the group-structure equality already suffices for U(1).
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
data SelectedSU2HostAutomaticallyIdentifiesBrownMaclayStress : Set where

tableEntryDoesNotChooseCandidateGroup :
  Sprint105SU2EntryAutomaticallyIdentifiesUnifiedCandidateGroup → ⊥
tableEntryDoesNotChooseCandidateGroup ()

quaternionSU2DoesNotChooseCandidateGroup :
  QuaternionSU2AutomaticallyChoosesUnifiedCandidateGroup → ⊥
quaternionSU2DoesNotChooseCandidateGroup ()

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
    true true true true true true true true false false
    false false false false

casimirSelectedQFTSU2HostReading : String
casimirSelectedQFTSU2HostReading =
  "The load-bearing host is now only same-target compact simplicity plus literal interpretation as the existing quaternionic SU(2) GroupStructure. That equality is sufficient to transport the canonical U(1) torus inclusion into the selected carrier. Dynkin-A1 and Sprint105 SU2 labels remain optional consistency metadata, not independent Casimir host blockers. Compact simplicity itself needs no new mathematics once either an existing pinned physical YM construction on the same qftCarriers/qftSemantics or a same-object LiteralClayStructuralBase for the selected qftTarget is attached. None of this identifies Brown-Maclay stress."
