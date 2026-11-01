module DASHI.Physics.Closure.ObservableTransportGaugeEntry where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Theorem-thin observable transport gate.
--
-- This module only records the admissibility surface needed to treat an
-- observable transport as a possible gauge-entry point.  It does not choose a
-- gauge group, recover matter, or assert a Standard Model classification.

data GaugeEntryStatus : Set where
  forced : GaugeEntryStatus
  conditional : GaugeEntryStatus
  failed : GaugeEntryStatus
  held : GaugeEntryStatus

record ObservableTransportCarriers
  {ℓO ℓP : Level} : Set (lsuc (ℓO ⊔ ℓP)) where
  field
    ObservableCarrier : Set ℓO
    PhysicsCarrier : Set ℓP

open ObservableTransportCarriers public

record ObservableTransportContract
  {ℓO ℓP ℓA ℓS ℓC : Level}
  (carriers : ObservableTransportCarriers {ℓO} {ℓP})
    : Set (lsuc (ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC)) where
  field
    transport :
      PhysicsCarrier carriers →
      ObservableCarrier carriers

    observableProjection :
      ObservableCarrier carriers →
      ObservableCarrier carriers

    admissible :
      PhysicsCarrier carriers →
      Set ℓA

    transportStable :
      (p : PhysicsCarrier carriers) →
      admissible p →
      Set ℓS

    projectionCoherent :
      (p : PhysicsCarrier carriers) →
      admissible p →
      Set ℓC

open ObservableTransportContract public

record ObservableTransportGaugeEntry
  {ℓO ℓP ℓA ℓS ℓC ℓB : Level}
  {carriers : ObservableTransportCarriers {ℓO} {ℓP}}
  (contract : ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} carriers)
    : Set (lsuc (ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC ⊔ ℓB)) where
  field
    gaugeEntryBoundary :
      PhysicsCarrier carriers →
      Set ℓB

    status :
      PhysicsCarrier carriers →
      GaugeEntryStatus

    admissibilityWitness :
      (p : PhysicsCarrier carriers) →
      status p ≡ forced →
      admissible contract p

    stabilityWitness :
      (p : PhysicsCarrier carriers) →
      (a : admissible contract p) →
      transportStable contract p a

    coherenceWitness :
      (p : PhysicsCarrier carriers) →
      (a : admissible contract p) →
      projectionCoherent contract p a

open ObservableTransportGaugeEntry public

record ForcedGaugeEntry
  {ℓO ℓP ℓA ℓS ℓC ℓB : Level}
  {carriers : ObservableTransportCarriers {ℓO} {ℓP}}
  {contract : ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} carriers}
  (gate : ObservableTransportGaugeEntry {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB} contract)
  (p : PhysicsCarrier carriers)
    : Set (ℓA ⊔ ℓS ⊔ ℓC) where
  field
    forcedStatus :
      status gate p ≡ forced

    admissibleAtEntry :
      admissible contract p

    stableAtEntry :
      transportStable contract p admissibleAtEntry

    coherentAtEntry :
      projectionCoherent contract p admissibleAtEntry

open ForcedGaugeEntry public

forcedEntryFromGate :
  {ℓO ℓP ℓA ℓS ℓC ℓB : Level}
  {carriers : ObservableTransportCarriers {ℓO} {ℓP}}
  {contract : ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} carriers}
  (gate : ObservableTransportGaugeEntry {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB} contract) →
  (p : PhysicsCarrier carriers) →
  status gate p ≡ forced →
  ForcedGaugeEntry gate p
forcedEntryFromGate gate p forcedStatus =
  record
    { forcedStatus = forcedStatus
    ; admissibleAtEntry = admissibilityWitness gate p forcedStatus
    ; stableAtEntry =
        stabilityWitness gate p (admissibilityWitness gate p forcedStatus)
    ; coherentAtEntry =
        coherenceWitness gate p (admissibilityWitness gate p forcedStatus)
    }

record GaugeEntryClassification
  {ℓO ℓP ℓA ℓS ℓC ℓB : Level}
  {carriers : ObservableTransportCarriers {ℓO} {ℓP}}
  {contract : ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} carriers}
  (gate : ObservableTransportGaugeEntry {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB} contract)
  (p : PhysicsCarrier carriers)
    : Set where
  field
    classifiedAs : GaugeEntryStatus
    classificationAgrees : status gate p ≡ classifiedAs

open GaugeEntryClassification public

classifyGaugeEntry :
  {ℓO ℓP ℓA ℓS ℓC ℓB : Level}
  {carriers : ObservableTransportCarriers {ℓO} {ℓP}}
  {contract : ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} carriers}
  (gate : ObservableTransportGaugeEntry {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB} contract) →
  (p : PhysicsCarrier carriers) →
  GaugeEntryClassification gate p
classifyGaugeEntry gate p =
  record
    { classifiedAs = status gate p
    ; classificationAgrees = refl
    }
