module DASHI.Physics.QFT.Gate6FinitePrimeLaneLocalEndomorphismCategory where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger

------------------------------------------------------------------------
-- Gate 6 finite prime-lane localised endomorphism category.
--
-- This module is intentionally finite and lane-local.  It consumes the
-- p2/p3/p5 rows and the finite DHR arrow ledger, then packages the identity
-- endomorphism fibre over each row as a category.  It does not promote an
-- arbitrary-sector DHR category, construct End(rho_pk) ~= Rep(G_pk), or add
-- any postulated local-algebra action.

data Gate6FinitePrimeLane : Set where
  gate6-p2 :
    Gate6FinitePrimeLane

  gate6-p3 :
    Gate6FinitePrimeLane

  gate6-p5 :
    Gate6FinitePrimeLane

gate6FinitePrimeLaneRow :
  Gate6FinitePrimeLane →
  Ledger.FinitePrimeLaneSMRow
gate6FinitePrimeLaneRow gate6-p2 =
  Ledger.p2U1YFinitePrimeLaneSMRow
gate6FinitePrimeLaneRow gate6-p3 =
  Ledger.p3SU2LFinitePrimeLaneSMRow
gate6FinitePrimeLaneRow gate6-p5 =
  Ledger.p5SU3cFinitePrimeLaneSMRow

data Gate6LocalisedEndomorphism
  (lane : Gate6FinitePrimeLane) :
  Set where
  gate6LocalIdentityEndomorphism :
    Gate6LocalisedEndomorphism lane

gate6LocalEndomorphismToLedgerArrow :
  {lane : Gate6FinitePrimeLane} →
  Gate6LocalisedEndomorphism lane →
  Ledger.FinitePrimeLaneDHRArrow
    (gate6FinitePrimeLaneRow lane)
    (gate6FinitePrimeLaneRow lane)
gate6LocalEndomorphismToLedgerArrow
  {lane}
  gate6LocalIdentityEndomorphism =
  Ledger.finitePrimeLaneId
    (gate6FinitePrimeLaneRow lane)

gate6LocalIdentity :
  (lane : Gate6FinitePrimeLane) →
  Gate6LocalisedEndomorphism lane
gate6LocalIdentity lane =
  gate6LocalIdentityEndomorphism

gate6LocalCompose :
  {lane : Gate6FinitePrimeLane} →
  Gate6LocalisedEndomorphism lane →
  Gate6LocalisedEndomorphism lane →
  Gate6LocalisedEndomorphism lane
gate6LocalCompose gate6LocalIdentityEndomorphism gate6LocalIdentityEndomorphism =
  gate6LocalIdentityEndomorphism

gate6LocalComposeUsesLedger :
  {lane : Gate6FinitePrimeLane} →
  (g f : Gate6LocalisedEndomorphism lane) →
  gate6LocalEndomorphismToLedgerArrow (gate6LocalCompose g f)
  ≡
  Ledger.finitePrimeLaneDHRCompose
    (gate6LocalEndomorphismToLedgerArrow g)
    (gate6LocalEndomorphismToLedgerArrow f)
gate6LocalComposeUsesLedger
  gate6LocalIdentityEndomorphism
  gate6LocalIdentityEndomorphism =
  refl

gate6LocalAssociativity :
  {lane : Gate6FinitePrimeLane} →
  (h g f : Gate6LocalisedEndomorphism lane) →
  gate6LocalCompose h (gate6LocalCompose g f)
  ≡
  gate6LocalCompose (gate6LocalCompose h g) f
gate6LocalAssociativity
  gate6LocalIdentityEndomorphism
  gate6LocalIdentityEndomorphism
  gate6LocalIdentityEndomorphism =
  refl

gate6LocalLeftIdentity :
  {lane : Gate6FinitePrimeLane} →
  (f : Gate6LocalisedEndomorphism lane) →
  gate6LocalCompose (gate6LocalIdentity lane) f
  ≡
  f
gate6LocalLeftIdentity gate6LocalIdentityEndomorphism =
  refl

gate6LocalRightIdentity :
  {lane : Gate6FinitePrimeLane} →
  (f : Gate6LocalisedEndomorphism lane) →
  gate6LocalCompose f (gate6LocalIdentity lane)
  ≡
  f
gate6LocalRightIdentity gate6LocalIdentityEndomorphism =
  refl

record Gate6FinitePrimeLaneLocalEndomorphismCategoryRow
  (lane : Gate6FinitePrimeLane) :
  Setω where
  field
    finiteRow :
      Ledger.FinitePrimeLaneSMRow

    finiteRowIsLedgerRow :
      finiteRow ≡ gate6FinitePrimeLaneRow lane

    identityEndomorphism :
      Gate6LocalisedEndomorphism lane

    identityEndomorphismIsCanonical :
      identityEndomorphism ≡ gate6LocalIdentity lane

    composeEndomorphisms :
      Gate6LocalisedEndomorphism lane →
      Gate6LocalisedEndomorphism lane →
      Gate6LocalisedEndomorphism lane

    compositionIsLedgerLocalComposition :
      (g f : Gate6LocalisedEndomorphism lane) →
      gate6LocalEndomorphismToLedgerArrow (composeEndomorphisms g f)
      ≡
      Ledger.finitePrimeLaneDHRCompose
        (gate6LocalEndomorphismToLedgerArrow g)
        (gate6LocalEndomorphismToLedgerArrow f)

    associativityLaw :
      (h g f : Gate6LocalisedEndomorphism lane) →
      composeEndomorphisms h (composeEndomorphisms g f)
      ≡
      composeEndomorphisms (composeEndomorphisms h g) f

    leftIdentityLaw :
      (f : Gate6LocalisedEndomorphism lane) →
      composeEndomorphisms identityEndomorphism f
      ≡
      f

    rightIdentityLaw :
      (f : Gate6LocalisedEndomorphism lane) →
      composeEndomorphisms f identityEndomorphism
      ≡
      f

    ledgerIdentityLaw :
      Ledger.finitePrimeLaneDHRCompose
        (gate6LocalEndomorphismToLedgerArrow identityEndomorphism)
        (gate6LocalEndomorphismToLedgerArrow identityEndomorphism)
      ≡
      gate6LocalEndomorphismToLedgerArrow identityEndomorphism

    identityAvailable :
      Bool

    identityAvailableIsTrue :
      identityAvailable ≡ true

    compositionAvailable :
      Bool

    compositionAvailableIsTrue :
      compositionAvailable ≡ true

    associativityAvailable :
      Bool

    associativityAvailableIsTrue :
      associativityAvailable ≡ true

    arbitrarySectorPromoted :
      Bool

    arbitrarySectorPromotedIsFalse :
      arbitrarySectorPromoted ≡ false

    rowBoundary :
      List String

open Gate6FinitePrimeLaneLocalEndomorphismCategoryRow public

gate6FinitePrimeLaneLocalEndomorphismCategoryRow :
  (lane : Gate6FinitePrimeLane) →
  Gate6FinitePrimeLaneLocalEndomorphismCategoryRow lane
gate6FinitePrimeLaneLocalEndomorphismCategoryRow lane =
  record
    { finiteRow =
        gate6FinitePrimeLaneRow lane
    ; finiteRowIsLedgerRow =
        refl
    ; identityEndomorphism =
        gate6LocalIdentity lane
    ; identityEndomorphismIsCanonical =
        refl
    ; composeEndomorphisms =
        gate6LocalCompose
    ; compositionIsLedgerLocalComposition =
        gate6LocalComposeUsesLedger
    ; associativityLaw =
        gate6LocalAssociativity
    ; leftIdentityLaw =
        gate6LocalLeftIdentity
    ; rightIdentityLaw =
        gate6LocalRightIdentity
    ; ledgerIdentityLaw =
        refl
    ; identityAvailable =
        true
    ; identityAvailableIsTrue =
        refl
    ; compositionAvailable =
        true
    ; compositionAvailableIsTrue =
        refl
    ; associativityAvailable =
        true
    ; associativityAvailableIsTrue =
        refl
    ; arbitrarySectorPromoted =
        false
    ; arbitrarySectorPromotedIsFalse =
        refl
    ; rowBoundary =
        "Gate 6 finite local endomorphism row consumes the existing p2/p3/p5 finite ledger row"
        ∷ "The only local endomorphism exposed here is the ledger identity arrow over that row"
        ∷ "Composition, associativity, and left/right identity are finite-row laws only"
        ∷ "No arbitrary DHR sector category, End(rho_pk) ~= Rep(G_pk), or local-algebra action is promoted"
        ∷ []
    }

p2Gate6LocalEndomorphismCategoryRow :
  Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p2
p2Gate6LocalEndomorphismCategoryRow =
  gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p2

p3Gate6LocalEndomorphismCategoryRow :
  Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p3
p3Gate6LocalEndomorphismCategoryRow =
  gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p3

p5Gate6LocalEndomorphismCategoryRow :
  Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p5
p5Gate6LocalEndomorphismCategoryRow =
  gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p5

record Gate6FinitePrimeLaneLocalEndomorphismCategoryLedger : Setω where
  field
    p2Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p2

    p3Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p3

    p5Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p5

    sourceLedger :
      Ledger.FinitePrimeLaneDHRSMNaturalityReceipt

    sourceLedgerCanonicalRecorded :
      Bool

    sourceLedgerCanonicalRecordedIsTrue :
      sourceLedgerCanonicalRecorded ≡ true

    p2CategoryLawsAvailable :
      Bool

    p2CategoryLawsAvailableIsTrue :
      p2CategoryLawsAvailable ≡ true

    p3CategoryLawsAvailable :
      Bool

    p3CategoryLawsAvailableIsTrue :
      p3CategoryLawsAvailable ≡ true

    p5CategoryLawsAvailable :
      Bool

    p5CategoryLawsAvailableIsTrue :
      p5CategoryLawsAvailable ≡ true

    arbitrarySectorCategoryPromoted :
      Bool

    arbitrarySectorCategoryPromotedIsFalse :
      arbitrarySectorCategoryPromoted ≡ false

    ledgerBoundary :
      List String

open Gate6FinitePrimeLaneLocalEndomorphismCategoryLedger public

canonicalGate6FinitePrimeLaneLocalEndomorphismCategoryLedger :
  Gate6FinitePrimeLaneLocalEndomorphismCategoryLedger
canonicalGate6FinitePrimeLaneLocalEndomorphismCategoryLedger =
  record
    { p2Row =
        p2Gate6LocalEndomorphismCategoryRow
    ; p3Row =
        p3Gate6LocalEndomorphismCategoryRow
    ; p5Row =
        p5Gate6LocalEndomorphismCategoryRow
    ; sourceLedger =
        Ledger.canonicalFinitePrimeLaneDHRSMNaturalityReceipt
    ; sourceLedgerCanonicalRecorded =
        true
    ; sourceLedgerCanonicalRecordedIsTrue =
        refl
    ; p2CategoryLawsAvailable =
        true
    ; p2CategoryLawsAvailableIsTrue =
        refl
    ; p3CategoryLawsAvailable =
        true
    ; p3CategoryLawsAvailableIsTrue =
        refl
    ; p5CategoryLawsAvailable =
        true
    ; p5CategoryLawsAvailableIsTrue =
        refl
    ; arbitrarySectorCategoryPromoted =
        false
    ; arbitrarySectorCategoryPromotedIsFalse =
        refl
    ; ledgerBoundary =
        "The source ledger is the existing finite p2/p3/p5 DHR-SM compatibility/naturality receipt"
        ∷ "Each lane row carries identity, composition, associativity, left identity, and right identity"
        ∷ "The construction is finite and localised to the three ledger rows"
        ∷ "Arbitrary-sector category promotion remains false"
        ∷ []
    }
