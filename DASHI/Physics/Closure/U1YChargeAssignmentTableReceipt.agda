module DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt as HAnomaly

------------------------------------------------------------------------
-- U(1)_Y charge assignment table.
--
-- This receipt records the physical 48-Weyl-fermion hypercharge table.
-- The anomaly receipts use the standard all-left-handed convention with
-- conjugate multiplets u^c, d^c, e^c, nu^c; this file records both the
-- physical signs and the anomaly-convention bridge explicitly.

data PhysicalHyperchargeMultiplet : Set where
  qL :
    PhysicalHyperchargeMultiplet

  uR :
    PhysicalHyperchargeMultiplet

  dR :
    PhysicalHyperchargeMultiplet

  leptonL :
    PhysicalHyperchargeMultiplet

  eR :
    PhysicalHyperchargeMultiplet

  nuR :
    PhysicalHyperchargeMultiplet

canonicalPhysicalMultiplets :
  List PhysicalHyperchargeMultiplet
canonicalPhysicalMultiplets =
  qL
  ∷ uR
  ∷ dR
  ∷ leptonL
  ∷ eR
  ∷ nuR
  ∷ []

physicalSignedSixths :
  PhysicalHyperchargeMultiplet →
  ℤ
physicalSignedSixths qL =
  + 1
physicalSignedSixths uR =
  + 4
physicalSignedSixths dR =
  -[1+ 1 ]
physicalSignedSixths leptonL =
  -[1+ 2 ]
physicalSignedSixths eR =
  -[1+ 5 ]
physicalSignedSixths nuR =
  + 0

physicalWeylCount :
  PhysicalHyperchargeMultiplet →
  Nat
physicalWeylCount qL =
  18
physicalWeylCount uR =
  9
physicalWeylCount dR =
  9
physicalWeylCount leptonL =
  6
physicalWeylCount eR =
  3
physicalWeylCount nuR =
  3

physicalChargeLabel :
  PhysicalHyperchargeMultiplet →
  String
physicalChargeLabel qL =
  "Q_L: 18 Weyl states, Y=+1/6"
physicalChargeLabel uR =
  "u_R: 9 Weyl states, Y=+2/3"
physicalChargeLabel dR =
  "d_R: 9 Weyl states, Y=-1/3"
physicalChargeLabel leptonL =
  "L_L: 6 Weyl states, Y=-1/2"
physicalChargeLabel eR =
  "e_R: 3 Weyl states, Y=-1"
physicalChargeLabel nuR =
  "nu_R: 3 Weyl states, Y=0"

record PhysicalHyperchargeEntry : Set where
  field
    multiplet :
      PhysicalHyperchargeMultiplet

    label :
      String

    labelIsCanonical :
      label ≡ physicalChargeLabel multiplet

    signedSixths :
      ℤ

    signedSixthsArePhysical :
      signedSixths ≡ physicalSignedSixths multiplet

    weylCount :
      Nat

    weylCountIsPhysical :
      weylCount ≡ physicalWeylCount multiplet

open PhysicalHyperchargeEntry public

qLPhysicalEntry :
  PhysicalHyperchargeEntry
qLPhysicalEntry =
  record
    { multiplet = qL
    ; label = physicalChargeLabel qL
    ; labelIsCanonical = refl
    ; signedSixths = + 1
    ; signedSixthsArePhysical = refl
    ; weylCount = 18
    ; weylCountIsPhysical = refl
    }

uRPhysicalEntry :
  PhysicalHyperchargeEntry
uRPhysicalEntry =
  record
    { multiplet = uR
    ; label = physicalChargeLabel uR
    ; labelIsCanonical = refl
    ; signedSixths = + 4
    ; signedSixthsArePhysical = refl
    ; weylCount = 9
    ; weylCountIsPhysical = refl
    }

dRPhysicalEntry :
  PhysicalHyperchargeEntry
dRPhysicalEntry =
  record
    { multiplet = dR
    ; label = physicalChargeLabel dR
    ; labelIsCanonical = refl
    ; signedSixths = -[1+ 1 ]
    ; signedSixthsArePhysical = refl
    ; weylCount = 9
    ; weylCountIsPhysical = refl
    }

leptonLPhysicalEntry :
  PhysicalHyperchargeEntry
leptonLPhysicalEntry =
  record
    { multiplet = leptonL
    ; label = physicalChargeLabel leptonL
    ; labelIsCanonical = refl
    ; signedSixths = -[1+ 2 ]
    ; signedSixthsArePhysical = refl
    ; weylCount = 6
    ; weylCountIsPhysical = refl
    }

eRPhysicalEntry :
  PhysicalHyperchargeEntry
eRPhysicalEntry =
  record
    { multiplet = eR
    ; label = physicalChargeLabel eR
    ; labelIsCanonical = refl
    ; signedSixths = -[1+ 5 ]
    ; signedSixthsArePhysical = refl
    ; weylCount = 3
    ; weylCountIsPhysical = refl
    }

nuRPhysicalEntry :
  PhysicalHyperchargeEntry
nuRPhysicalEntry =
  record
    { multiplet = nuR
    ; label = physicalChargeLabel nuR
    ; labelIsCanonical = refl
    ; signedSixths = + 0
    ; signedSixthsArePhysical = refl
    ; weylCount = 3
    ; weylCountIsPhysical = refl
    }

canonicalPhysicalHyperchargeTable :
  List PhysicalHyperchargeEntry
canonicalPhysicalHyperchargeTable =
  qLPhysicalEntry
  ∷ uRPhysicalEntry
  ∷ dRPhysicalEntry
  ∷ leptonLPhysicalEntry
  ∷ eRPhysicalEntry
  ∷ nuRPhysicalEntry
  ∷ []

totalPhysicalWeylCount :
  Nat
totalPhysicalWeylCount =
  48

leftHandedAnomalyConvention :
  String
leftHandedAnomalyConvention =
  "Anomaly sums are computed with left-handed conjugates: u^c has Y=-2/3, d^c has Y=+1/3, e^c has Y=+1, and nu^c has Y=0"

physicalToAnomalyConventionBridge :
  String
physicalToAnomalyConventionBridge =
  "Physical right-handed fields are replaced by left-handed conjugates for anomaly calculations, reversing their U(1)_Y signs and using conjugate colour representations"

record U1YChargeAssignmentTableReceipt : Setω where
  field
    hyperchargeUnitDenominator :
      Nat

    hyperchargeUnitDenominatorIsSix :
      hyperchargeUnitDenominator ≡ 6

    physicalTable :
      List PhysicalHyperchargeEntry

    physicalTableIsCanonical :
      physicalTable ≡ canonicalPhysicalHyperchargeTable

    totalWeylCount :
      Nat

    totalWeylCountIs48 :
      totalWeylCount ≡ totalPhysicalWeylCount

    qLCount :
      physicalWeylCount qL ≡ 18

    uRCount :
      physicalWeylCount uR ≡ 9

    dRCount :
      physicalWeylCount dR ≡ 9

    leptonLCount :
      physicalWeylCount leptonL ≡ 6

    eRCount :
      physicalWeylCount eR ≡ 3

    nuRCount :
      physicalWeylCount nuR ≡ 3

    physicalChargesMatchSM :
      Bool

    physicalChargesMatchSMIsTrue :
      physicalChargesMatchSM ≡ true

    anomalyConvention :
      String

    anomalyConventionIsCanonical :
      anomalyConvention ≡ leftHandedAnomalyConvention

    conventionBridge :
      String

    conventionBridgeIsCanonical :
      conventionBridge ≡ physicalToAnomalyConventionBridge

    anomalyLedger :
      List HAnomaly.HyperchargeLedgerEntry

    anomalyLedgerIsCanonical :
      anomalyLedger ≡ HAnomaly.canonicalHyperchargeLedger

    exactCarrierDerivationPromoted :
      Bool

    exactCarrierDerivationPromotedIsFalse :
      exactCarrierDerivationPromoted ≡ false

    inheritedCandidateStatus :
      Bool

    inheritedCandidateStatusIsTrue :
      inheritedCandidateStatus ≡ true

    gDHREqualsGSM :
      Bool

    gDHREqualsGSMIsFalse :
      gDHREqualsGSM ≡ false

    exactDHRPromoted :
      Bool

    exactDHRPromotedIsFalse :
      exactDHRPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    auditTrail :
      List String

open U1YChargeAssignmentTableReceipt public

canonicalU1YChargeAssignmentTableReceipt :
  U1YChargeAssignmentTableReceipt
canonicalU1YChargeAssignmentTableReceipt =
  record
    { hyperchargeUnitDenominator =
        6
    ; hyperchargeUnitDenominatorIsSix =
        refl
    ; physicalTable =
        canonicalPhysicalHyperchargeTable
    ; physicalTableIsCanonical =
        refl
    ; totalWeylCount =
        48
    ; totalWeylCountIs48 =
        refl
    ; qLCount =
        refl
    ; uRCount =
        refl
    ; dRCount =
        refl
    ; leptonLCount =
        refl
    ; eRCount =
        refl
    ; nuRCount =
        refl
    ; physicalChargesMatchSM =
        true
    ; physicalChargesMatchSMIsTrue =
        refl
    ; anomalyConvention =
        leftHandedAnomalyConvention
    ; anomalyConventionIsCanonical =
        refl
    ; conventionBridge =
        physicalToAnomalyConventionBridge
    ; conventionBridgeIsCanonical =
        refl
    ; anomalyLedger =
        HAnomaly.canonicalHyperchargeLedger
    ; anomalyLedgerIsCanonical =
        refl
    ; exactCarrierDerivationPromoted =
        false
    ; exactCarrierDerivationPromotedIsFalse =
        refl
    ; inheritedCandidateStatus =
        true
    ; inheritedCandidateStatusIsTrue =
        refl
    ; gDHREqualsGSM =
        false
    ; gDHREqualsGSMIsFalse =
        refl
    ; exactDHRPromoted =
        false
    ; exactDHRPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; auditTrail =
        "Physical table totals 48 Weyl states: 18 + 9 + 9 + 6 + 3 + 3"
        ∷ "Anomaly verification uses the left-handed conjugate convention, not the physical right-handed signs"
        ∷ "The table records the SM assignment selected by the carrier U(1)_Y candidate; it does not promote an exact SM, DHR, Clay, or terminal claim"
        ∷ []
    }

u1YChargeTableHas48WeylStates :
  totalWeylCount canonicalU1YChargeAssignmentTableReceipt ≡ 48
u1YChargeTableHas48WeylStates =
  refl

u1YChargeTablePromotionFalse :
  exactCarrierDerivationPromoted canonicalU1YChargeAssignmentTableReceipt
  ≡
  false
u1YChargeTablePromotionFalse =
  refl

u1YChargeTableKeepsGDHRGSMFalse :
  gDHREqualsGSM canonicalU1YChargeAssignmentTableReceipt
  ≡
  false
u1YChargeTableKeepsGDHRGSMFalse =
  refl

u1YChargeTableTerminalPromotionFalse :
  terminalClaimPromoted canonicalU1YChargeAssignmentTableReceipt
  ≡
  false
u1YChargeTableTerminalPromotionFalse =
  refl
