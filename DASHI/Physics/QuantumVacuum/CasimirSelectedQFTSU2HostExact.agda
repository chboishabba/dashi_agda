module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1
import DASHI.Physics.Closure.YMSprint105CompactSimpleGroupParameterTable as Table

------------------------------------------------------------------------
-- SELECTED QFT GROUP -> THE REPOSITORY'S CONCRETE SU(2) HOST
--
-- Two SU(2) surfaces already exist independently:
--
--   * the literal unit-quaternion GroupStructure used by the gauge stack;
--   * the Sprint105 compact-simple parameter-table entry `SU2`.
--
-- UnifiedCandidate deliberately leaves CompactSimpleGroup abstract.  Therefore
-- choosing a group token does not definitionally identify it with either SU(2)
-- surface.  This record is the missing interpretation receipt.  It is stronger
-- than a string/tag: an interpretation of every candidate group token as a
-- GroupStructure is supplied and the selected token is proved equal to the
-- exact unit-quaternion SU(2) GroupStructure.
------------------------------------------------------------------------

record CasimirSelectedQFTSU2Host
    (U : Weld.UnifiedCandidate)
    (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    selectedGroupIsCompactSimple :
      QFT.IsCompactSimple (Weld.qftSemantics U) group

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

selectedGroupCarrierIsQuaternionSU2 :
  ∀ {U : Weld.UnifiedCandidate}
    {group : QFT.CompactSimpleGroup (Weld.qftCarriers U)} →
  (host : CasimirSelectedQFTSU2Host U group) →
  Gauge.Carrier (groupStructureInterpretation host group) ≡ SU2.SU2Quaternion
selectedGroupCarrierIsQuaternionSU2 host =
  cong Gauge.Carrier (selectedGroupStructureIsQuaternionSU2 host)

-- Once the host interpretation is paid, the already-proved U(1)->SU(2)
-- inclusion can be transported into the selected QFT group's interpreted
-- carrier without a second group theorem.
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

------------------------------------------------------------------------
-- Reuse both existing SU(2) authorities directly.
------------------------------------------------------------------------

concreteQuaternionSU2Group : Gauge.GroupStructure
concreteQuaternionSU2Group = SU2.su2QuaternionGroup

canonicalSU2ParameterEntry : Table.CompactSimpleGroupEntry
canonicalSU2ParameterEntry = Table.SU2

canonicalSU2ParameterRow : Table.GroupParameterRow
canonicalSU2ParameterRow = Table.su2ParameterRow

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Machine-readable boundary.
------------------------------------------------------------------------

record CasimirSelectedQFTSU2HostBoundary : Set where
  constructor casimir-selected-qft-su2-host-boundary
  field
    concreteQuaternionSU2GroupOwned : Bool
    sprint105SU2EntryOwned : Bool
    selectedQFTSU2HostInterfaceOwned : Bool
    literalU1InclusionCompilerOwnedAfterHost : Bool

    selectedGroupCompactSimpleWitnessPaid : Bool
    selectedGroupClassifiedAsSprint105SU2Paid : Bool
    selectedGroupInterpretedAsQuaternionSU2Paid : Bool
    brownMaclayStressIdentifiedByHostAlone : Bool

open CasimirSelectedQFTSU2HostBoundary public

canonicalCasimirSelectedQFTSU2HostBoundary :
  CasimirSelectedQFTSU2HostBoundary
canonicalCasimirSelectedQFTSU2HostBoundary =
  casimir-selected-qft-su2-host-boundary
    true true true true
    false false false false

casimirSelectedQFTSU2HostReading : String
casimirSelectedQFTSU2HostReading =
  "The repository already owns both a concrete unit-quaternion SU(2) GroupStructure and a Sprint105 SU2 compact-simple table entry. UnifiedCandidate's CompactSimpleGroup remains an abstract token carrier, so the missing Casimir host payment is an interpretation/classification receipt for one selected token: prove it satisfies the candidate semantics' IsCompactSimple predicate, classify it as Sprint105 SU2, and prove its interpreted GroupStructure is exactly su2QuaternionGroup. After that receipt the existing U1TorusElement -> SU2Quaternion inclusion transports directly into the selected group's carrier. This group-host payment alone does not identify the selected QFT stress with Brown-Maclay."
