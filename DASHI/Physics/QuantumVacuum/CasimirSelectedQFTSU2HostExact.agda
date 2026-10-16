module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsCompactSimpleGroupPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Physics.Closure.YMSprint105CompactSimpleGroupParameterTable as Table

------------------------------------------------------------------------
-- SELECTED QFT GROUP -> SOURCE-BACKED A1 / CONCRETE SU(2) HOST
--
-- Required host data is exactly:
--   1. IsCompactSimple under the UnifiedCandidate semantics;
--   2. source-backed compact-simple data classifying the token as Dynkin A1;
--   3. interpretation of that exact token as the literal quaternionic SU(2)
--      GroupStructure used by the gauge stack.
--
-- Sprint105 SU2 remains a finite-table consistency reference only; it is not a
-- required classification field because the table does not faithfully interpret
-- UnifiedCandidate group tokens.
------------------------------------------------------------------------

record CasimirSelectedQFTSU2Host
    (U : Weld.UnifiedCandidate)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    selectedGroupIsCompactSimple :
      QFT.IsCompactSimple (Weld.qftSemantics U) group

    compactSimpleDataForGroup :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Promotion.CompactSimpleYMData
        (QFT.CompactSimpleGroup (Weld.qftCarriers U))

    selectedGroupDynkinFamilyIsA1 :
      Promotion.family (compactSimpleDataForGroup group)
      ≡ Promotion.familyA 1

    groupStructureInterpretation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure

    selectedGroupStructureIsQuaternionSU2 :
      groupStructureInterpretation group ≡ SU2.su2QuaternionGroup

    reading : String

open CasimirSelectedQFTSU2Host public

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

hostFromPinnedYMConstruction :
  ∀ {U : Weld.UnifiedCandidate}
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U))
    (compactData :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Promotion.CompactSimpleYMData
        (QFT.CompactSimpleGroup (Weld.qftCarriers U))) →
  Promotion.family (compactData group) ≡ Promotion.familyA 1 →
  (interpretation :
    QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure) →
  interpretation group ≡ SU2.su2QuaternionGroup →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromPinnedYMConstruction
    pinned group compactData familyA1 interpretation interpreted reading = record
  { selectedGroupIsCompactSimple =
      compactSimpleFromPinnedYMConstruction pinned group
  ; compactSimpleDataForGroup = compactData
  ; selectedGroupDynkinFamilyIsA1 = familyA1
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
    sprint105ClassificationIsSecondaryConsistencyTag : Bool
    sprint105ClassificationRequiredForHost : Bool

    selectedGroupCompactSimpleWitnessPaid : Bool
    selectedGroupDynkinA1ClassificationPaid : Bool
    selectedGroupInterpretedAsQuaternionSU2Paid : Bool
    brownMaclayStressIdentifiedByHostAlone : Bool

open CasimirSelectedQFTSU2HostBoundary public

canonicalCasimirSelectedQFTSU2HostBoundary :
  CasimirSelectedQFTSU2HostBoundary
canonicalCasimirSelectedQFTSU2HostBoundary =
  casimir-selected-qft-su2-host-boundary
    true true true true true true true false
    false false false false

casimirSelectedQFTSU2HostReading : String
casimirSelectedQFTSU2HostReading =
  "The selected Casimir QFT host is now exactly IsCompactSimple + source-backed Dynkin A1 data + literal quaternionic SU(2) GroupStructure interpretation. Sprint105 SU2 is a secondary finite-table consistency reference and is explicitly not required to inhabit the host. A pinned physical YM construction on the same qftCarriers/qftSemantics supplies IsCompactSimple without a second theorem. Once the three required host receipts are paid, the existing U1 torus inclusion transports into the selected carrier. None of this identifies Brown-Maclay stress."
