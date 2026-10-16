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
-- Primary classification is now the compact-simple promotion owner's Dynkin
-- family, not the finite Sprint105 display table.  Sprint105 SU2 remains only a
-- secondary consistency tag.  The selected abstract QFT token must also map to
-- the literal unit-quaternion GroupStructure used by the gauge stack.
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

    -- Secondary table cross-check only; not the primary classification proof.
    parameterTableClassifier :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Table.CompactSimpleGroupEntry

    selectedGroupClassifiesAsSU2 :
      parameterTableClassifier group ≡ Table.SU2

    groupStructureInterpretation :
      QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure

    selectedGroupStructureIsQuaternionSU2 :
      groupStructureInterpretation group ≡ SU2.su2QuaternionGroup

    reading : String

open CasimirSelectedQFTSU2Host public

------------------------------------------------------------------------
-- Pinned physical YM already supplies IsCompactSimple on the SAME carrier and
-- semantics, so that leaf is compiler output whenever the pinned object exists.
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
  (classifier :
    QFT.CompactSimpleGroup (Weld.qftCarriers U) →
    Table.CompactSimpleGroupEntry) →
  classifier group ≡ Table.SU2 →
  (interpretation :
    QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure) →
  interpretation group ≡ SU2.su2QuaternionGroup →
  String →
  CasimirSelectedQFTSU2Host U group
hostFromPinnedYMConstruction
    pinned group compactData familyA1 classifier classified interpretation interpreted reading = record
  { selectedGroupIsCompactSimple =
      compactSimpleFromPinnedYMConstruction pinned group
  ; compactSimpleDataForGroup = compactData
  ; selectedGroupDynkinFamilyIsA1 = familyA1
  ; parameterTableClassifier = classifier
  ; selectedGroupClassifiesAsSU2 = classified
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

    selectedGroupCompactSimpleWitnessPaid : Bool
    selectedGroupDynkinA1ClassificationPaid : Bool
    selectedGroupClassifiedAsSprint105SU2Paid : Bool
    selectedGroupInterpretedAsQuaternionSU2Paid : Bool
    brownMaclayStressIdentifiedByHostAlone : Bool

open CasimirSelectedQFTSU2HostBoundary public

canonicalCasimirSelectedQFTSU2HostBoundary :
  CasimirSelectedQFTSU2HostBoundary
canonicalCasimirSelectedQFTSU2HostBoundary =
  casimir-selected-qft-su2-host-boundary
    true true true true true true true
    false false false false false

casimirSelectedQFTSU2HostReading : String
casimirSelectedQFTSU2HostReading =
  "The selected Casimir QFT host now uses the source-backed compact-simple promotion vocabulary: the exact selected token must be IsCompactSimple, carry CompactSimpleYMData whose Dynkin family is A1, and interpret to the repository's literal unit-quaternion su2QuaternionGroup. Sprint105 SU2 is retained only as a secondary finite-table consistency tag. A pinned physical YM construction on the same qftCarriers/qftSemantics supplies IsCompactSimple without a second theorem. After the host receipts, the existing U1 torus inclusion transports into the selected carrier. None of this identifies Brown-Maclay stress."
