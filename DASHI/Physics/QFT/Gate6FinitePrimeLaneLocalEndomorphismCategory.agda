module DASHI.Physics.QFT.Gate6FinitePrimeLaneLocalEndomorphismCategory where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
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

gate6FinitePrimeLaneLabel :
  Gate6FinitePrimeLane →
  String
gate6FinitePrimeLaneLabel gate6-p2 =
  "p2"
gate6FinitePrimeLaneLabel gate6-p3 =
  "p3"
gate6FinitePrimeLaneLabel gate6-p5 =
  "p5"

gate6FinitePrimeLaneGaugeLabel :
  Gate6FinitePrimeLane →
  String
gate6FinitePrimeLaneGaugeLabel gate6-p2 =
  "U1Y"
gate6FinitePrimeLaneGaugeLabel gate6-p3 =
  "SU2L"
gate6FinitePrimeLaneGaugeLabel gate6-p5 =
  "SU3c"

gate6FinitePrimeLaneSectorLabel :
  Gate6FinitePrimeLane →
  String
gate6FinitePrimeLaneSectorLabel gate6-p2 =
  "DHR-U1-sector"
gate6FinitePrimeLaneSectorLabel gate6-p3 =
  "DHR-SU2-sector"
gate6FinitePrimeLaneSectorLabel gate6-p5 =
  "DHR-SU3-frontier"

gate6FinitePrimeLaneQuantumDimension :
  Gate6FinitePrimeLane →
  Nat
gate6FinitePrimeLaneQuantumDimension lane =
  Ledger.FinitePrimeLaneSMRow.gaugeDimension
    (gate6FinitePrimeLaneRow lane)

gate6FinitePrimeLaneGaugeFactor :
  Gate6FinitePrimeLane →
  Ledger.PrimeLaneSMGaugeFactor
gate6FinitePrimeLaneGaugeFactor lane =
  Ledger.FinitePrimeLaneSMRow.gaugeFactor
    (gate6FinitePrimeLaneRow lane)

gate6FinitePrimeLaneSectorAtom :
  Gate6FinitePrimeLane →
  Ledger.DHR.DHRGaugeSectorAtom
gate6FinitePrimeLaneSectorAtom lane =
  Ledger.FinitePrimeLaneSMRow.sectorAtom
    (gate6FinitePrimeLaneRow lane)

data Gate6FinitePrimeLaneQuantumNumberField : Set where
  quantumPrimeLaneLabel :
    Gate6FinitePrimeLaneQuantumNumberField

  quantumGaugeFactorLabel :
    Gate6FinitePrimeLaneQuantumNumberField

  quantumGaugeDimension :
    Gate6FinitePrimeLaneQuantumNumberField

  quantumSectorAtom :
    Gate6FinitePrimeLaneQuantumNumberField

  quantumLocalIdentityEndomorphism :
    Gate6FinitePrimeLaneQuantumNumberField

canonicalGate6FinitePrimeLaneQuantumNumberFields :
  List Gate6FinitePrimeLaneQuantumNumberField
canonicalGate6FinitePrimeLaneQuantumNumberFields =
  quantumPrimeLaneLabel
  ∷ quantumGaugeFactorLabel
  ∷ quantumGaugeDimension
  ∷ quantumSectorAtom
  ∷ quantumLocalIdentityEndomorphism
  ∷ []

record Gate6FinitePrimeLaneQuantumNumbers
  (lane : Gate6FinitePrimeLane) :
  Setω where
  field
    finiteRow :
      Ledger.FinitePrimeLaneSMRow

    finiteRowIsLedgerRow :
      finiteRow ≡ gate6FinitePrimeLaneRow lane

    primeLaneLabel :
      String

    primeLaneLabelIsCanonical :
      primeLaneLabel ≡ gate6FinitePrimeLaneLabel lane

    gaugeFactor :
      Ledger.PrimeLaneSMGaugeFactor

    gaugeFactorIsLedgerFactor :
      gaugeFactor ≡ gate6FinitePrimeLaneGaugeFactor lane

    gaugeFactorLabel :
      String

    gaugeFactorLabelIsCanonical :
      gaugeFactorLabel ≡ gate6FinitePrimeLaneGaugeLabel lane

    quantumDimension :
      Nat

    quantumDimensionIsLedgerDimension :
      quantumDimension ≡ gate6FinitePrimeLaneQuantumDimension lane

    sectorAtom :
      Ledger.DHR.DHRGaugeSectorAtom

    sectorAtomIsLedgerAtom :
      sectorAtom ≡ gate6FinitePrimeLaneSectorAtom lane

    sectorLabel :
      String

    sectorLabelIsCanonical :
      sectorLabel ≡ gate6FinitePrimeLaneSectorLabel lane

    localIdentityEndomorphism :
      Gate6LocalisedEndomorphism lane

    localIdentityEndomorphismIsCanonical :
      localIdentityEndomorphism ≡ gate6LocalIdentity lane

    localIdentityArrow :
      Ledger.FinitePrimeLaneDHRArrow finiteRow finiteRow

    localIdentityArrowIsLedgerIdentity :
      localIdentityArrow ≡ Ledger.finitePrimeLaneId finiteRow

    quantumNumberFields :
      List Gate6FinitePrimeLaneQuantumNumberField

    quantumNumberFieldsAreCanonical :
      quantumNumberFields ≡ canonicalGate6FinitePrimeLaneQuantumNumberFields

    finiteLaneQuantumNumbersAvailable :
      Bool

    finiteLaneQuantumNumbersAvailableIsTrue :
      finiteLaneQuantumNumbersAvailable ≡ true

    arbitrarySectorQuantumNumbersPromoted :
      Bool

    arbitrarySectorQuantumNumbersPromotedIsFalse :
      arbitrarySectorQuantumNumbersPromoted ≡ false

    quantumNumberBoundary :
      List String

open Gate6FinitePrimeLaneQuantumNumbers public

gate6FinitePrimeLaneQuantumNumbers :
  (lane : Gate6FinitePrimeLane) →
  Gate6FinitePrimeLaneQuantumNumbers lane
gate6FinitePrimeLaneQuantumNumbers lane =
  record
    { finiteRow =
        gate6FinitePrimeLaneRow lane
    ; finiteRowIsLedgerRow =
        refl
    ; primeLaneLabel =
        gate6FinitePrimeLaneLabel lane
    ; primeLaneLabelIsCanonical =
        refl
    ; gaugeFactor =
        gate6FinitePrimeLaneGaugeFactor lane
    ; gaugeFactorIsLedgerFactor =
        refl
    ; gaugeFactorLabel =
        gate6FinitePrimeLaneGaugeLabel lane
    ; gaugeFactorLabelIsCanonical =
        refl
    ; quantumDimension =
        gate6FinitePrimeLaneQuantumDimension lane
    ; quantumDimensionIsLedgerDimension =
        refl
    ; sectorAtom =
        gate6FinitePrimeLaneSectorAtom lane
    ; sectorAtomIsLedgerAtom =
        refl
    ; sectorLabel =
        gate6FinitePrimeLaneSectorLabel lane
    ; sectorLabelIsCanonical =
        refl
    ; localIdentityEndomorphism =
        gate6LocalIdentity lane
    ; localIdentityEndomorphismIsCanonical =
        refl
    ; localIdentityArrow =
        Ledger.finitePrimeLaneId (gate6FinitePrimeLaneRow lane)
    ; localIdentityArrowIsLedgerIdentity =
        refl
    ; quantumNumberFields =
        canonicalGate6FinitePrimeLaneQuantumNumberFields
    ; quantumNumberFieldsAreCanonical =
        refl
    ; finiteLaneQuantumNumbersAvailable =
        true
    ; finiteLaneQuantumNumbersAvailableIsTrue =
        refl
    ; arbitrarySectorQuantumNumbersPromoted =
        false
    ; arbitrarySectorQuantumNumbersPromotedIsFalse =
        refl
    ; quantumNumberBoundary =
        "Quantum numbers are read from the finite p2/p3/p5 ledger row"
        ∷ "Each row exposes prime-lane label, gauge-factor label, gauge dimension, sector atom, and local identity"
        ∷ "The surface is reusable by Gate 1 compatibility consumers without promoting arbitrary DHR sectors"
        ∷ []
    }

p2Gate6FinitePrimeLaneQuantumNumbers :
  Gate6FinitePrimeLaneQuantumNumbers gate6-p2
p2Gate6FinitePrimeLaneQuantumNumbers =
  gate6FinitePrimeLaneQuantumNumbers gate6-p2

p3Gate6FinitePrimeLaneQuantumNumbers :
  Gate6FinitePrimeLaneQuantumNumbers gate6-p3
p3Gate6FinitePrimeLaneQuantumNumbers =
  gate6FinitePrimeLaneQuantumNumbers gate6-p3

p5Gate6FinitePrimeLaneQuantumNumbers :
  Gate6FinitePrimeLaneQuantumNumbers gate6-p5
p5Gate6FinitePrimeLaneQuantumNumbers =
  gate6FinitePrimeLaneQuantumNumbers gate6-p5

record Gate6FinitePrimeLaneCompatibilityPayload : Setω where
  field
    p2QuantumNumbers :
      Gate6FinitePrimeLaneQuantumNumbers gate6-p2

    p3QuantumNumbers :
      Gate6FinitePrimeLaneQuantumNumbers gate6-p3

    p5QuantumNumbers :
      Gate6FinitePrimeLaneQuantumNumbers gate6-p5

    quantumNumbersForLane :
      (lane : Gate6FinitePrimeLane) →
      Gate6FinitePrimeLaneQuantumNumbers lane

    p2CompatibilityRow :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p2

    p3CompatibilityRow :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p3

    p5CompatibilityRow :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p5

    gate1CompatibilityPrimitiveName :
      String

    gate1CompatibilityPrimitiveNameIsCanonical :
      gate1CompatibilityPrimitiveName
      ≡
      "missingDHRSectorCompatibilityPrimitiveWitness"

    finiteRowsReadyForGate1Consumer :
      Bool

    finiteRowsReadyForGate1ConsumerIsTrue :
      finiteRowsReadyForGate1Consumer ≡ true

    p2QuantumNumbersAvailable :
      finiteLaneQuantumNumbersAvailable p2QuantumNumbers ≡ true

    p3QuantumNumbersAvailable :
      finiteLaneQuantumNumbersAvailable p3QuantumNumbers ≡ true

    p5QuantumNumbersAvailable :
      finiteLaneQuantumNumbersAvailable p5QuantumNumbers ≡ true

    p2CategoryLawsAvailable :
      associativityAvailable p2CompatibilityRow ≡ true

    p3CategoryLawsAvailable :
      associativityAvailable p3CompatibilityRow ≡ true

    p5CategoryLawsAvailable :
      associativityAvailable p5CompatibilityRow ≡ true

    arbitrarySectorCompatibilityPromoted :
      Bool

    arbitrarySectorCompatibilityPromotedIsFalse :
      arbitrarySectorCompatibilityPromoted ≡ false

    compatibilityPayloadBoundary :
      List String

open Gate6FinitePrimeLaneCompatibilityPayload public

canonicalGate6FinitePrimeLaneCompatibilityPayload :
  Gate6FinitePrimeLaneCompatibilityPayload
canonicalGate6FinitePrimeLaneCompatibilityPayload =
  record
    { p2QuantumNumbers =
        p2Gate6FinitePrimeLaneQuantumNumbers
    ; p3QuantumNumbers =
        p3Gate6FinitePrimeLaneQuantumNumbers
    ; p5QuantumNumbers =
        p5Gate6FinitePrimeLaneQuantumNumbers
    ; quantumNumbersForLane =
        gate6FinitePrimeLaneQuantumNumbers
    ; p2CompatibilityRow =
        p2Gate6LocalEndomorphismCategoryRow
    ; p3CompatibilityRow =
        p3Gate6LocalEndomorphismCategoryRow
    ; p5CompatibilityRow =
        p5Gate6LocalEndomorphismCategoryRow
    ; gate1CompatibilityPrimitiveName =
        "missingDHRSectorCompatibilityPrimitiveWitness"
    ; gate1CompatibilityPrimitiveNameIsCanonical =
        refl
    ; finiteRowsReadyForGate1Consumer =
        true
    ; finiteRowsReadyForGate1ConsumerIsTrue =
        refl
    ; p2QuantumNumbersAvailable =
        refl
    ; p3QuantumNumbersAvailable =
        refl
    ; p5QuantumNumbersAvailable =
        refl
    ; p2CategoryLawsAvailable =
        refl
    ; p3CategoryLawsAvailable =
        refl
    ; p5CategoryLawsAvailable =
        refl
    ; arbitrarySectorCompatibilityPromoted =
        false
    ; arbitrarySectorCompatibilityPromotedIsFalse =
        refl
    ; compatibilityPayloadBoundary =
        "Gate 6 now exposes a typed finite-lane compatibility payload for Gate 1"
        ∷ "The payload bundles p2/p3/p5 quantum numbers with the existing finite local endomorphism category rows"
        ∷ "The named Gate 1 primitive remains a downstream consumer obligation, not a promoted arbitrary-sector theorem"
        ∷ []
    }

record Gate6FinitePrimeLaneLocalEndomorphismCategoryLedger : Setω where
  field
    p2Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p2

    p3Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p3

    p5Row :
      Gate6FinitePrimeLaneLocalEndomorphismCategoryRow gate6-p5

    compatibilityPayload :
      Gate6FinitePrimeLaneCompatibilityPayload

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

    finiteQuantumNumbersAvailable :
      Bool

    finiteQuantumNumbersAvailableIsTrue :
      finiteQuantumNumbersAvailable ≡ true

    gate1CompatibilityPayloadAvailable :
      Bool

    gate1CompatibilityPayloadAvailableIsTrue :
      gate1CompatibilityPayloadAvailable ≡ true

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
    ; compatibilityPayload =
        canonicalGate6FinitePrimeLaneCompatibilityPayload
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
    ; finiteQuantumNumbersAvailable =
        true
    ; finiteQuantumNumbersAvailableIsTrue =
        refl
    ; gate1CompatibilityPayloadAvailable =
        true
    ; gate1CompatibilityPayloadAvailableIsTrue =
        refl
    ; arbitrarySectorCategoryPromoted =
        false
    ; arbitrarySectorCategoryPromotedIsFalse =
        refl
    ; ledgerBoundary =
        "The source ledger is the existing finite p2/p3/p5 DHR-SM compatibility/naturality receipt"
        ∷ "Each lane row carries identity, composition, associativity, left identity, and right identity"
        ∷ "The ledger now also exposes finite-lane quantum numbers and a Gate 1 compatibility payload"
        ∷ "The construction is finite and localised to the three ledger rows"
        ∷ "Arbitrary-sector category promotion remains false"
        ∷ []
    }
