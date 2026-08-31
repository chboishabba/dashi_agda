module DASHI.Chemistry.TGO93PhEurPesticideMembershipExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED POSITIVE PESTICIDE MEMBERSHIP
--
-- Australian source:
--   Therapeutic Goods (Standard for Medicinal Cannabis) (TGO 93) Order 2017,
--   latest compilation F2022C01204 (06 Dec 2022), Schedule 1 item 5:
--   Pesticides / Ph Eur 2.8.13 / not more than the limits specified there.
--   https://www.legislation.gov.au/F2017L00286/latest
--
-- European Pharmacopoeia source surface recovered for chapter 2.8.13:
--   European Pharmacopoeia 11.0, chapter revision 01/2022:20813,
--   Table 2.8.13.-1.  The table explicitly includes the named pesticides below.
--
-- IMPORTANT: `AustralianPanelMembership` means an explicit Table 2.8.13.-1
-- member reached through the TGO 93 Schedule-1 incorporation route.  It does
-- NOT mean that a particular Australian laboratory actually ran a validated
-- method for that analyte on a particular batch.  Lab scope, extraction,
-- detector response, LOD/LOQ and batch result require separate receipts.
------------------------------------------------------------------------

data PhEurEdition : Set where
  phEur11_0Revision01_2022 : PhEurEdition

data NamedPesticide : Set where
  acephate
  alachlor
  aldrinDieldrinSum
  chlorpyriphosEthyl
  chlorpyriphosMethyl
  ddtSum
  deltamethrin
  diazinon
  : NamedPesticide

-- Exact integer carrier: micrograms per kilogram.  This avoids importing
-- floating-point arithmetic for table values stated in mg/kg.
tableLimitMicrogramsPerKg : NamedPesticide → Nat
tableLimitMicrogramsPerKg acephate = 100
tableLimitMicrogramsPerKg alachlor = 50
tableLimitMicrogramsPerKg aldrinDieldrinSum = 50
tableLimitMicrogramsPerKg chlorpyriphosEthyl = 200
tableLimitMicrogramsPerKg chlorpyriphosMethyl = 100
tableLimitMicrogramsPerKg ddtSum = 1000
tableLimitMicrogramsPerKg deltamethrin = 500
tableLimitMicrogramsPerKg diazinon = 500

record PhEurTableMembership (pesticide : NamedPesticide) : Set where
  constructor phEurTableMembership
  field
    edition : PhEurEdition
    chapterReference : String
    tableReference : String
    displayedNameReference : String
    limitMicrogramsPerKg : Nat
    exactLimit :
      limitMicrogramsPerKg ≡ tableLimitMicrogramsPerKg pesticide
    sourceReference : String

open PhEurTableMembership public

membership : (pesticide : NamedPesticide) → PhEurTableMembership pesticide
membership acephate = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Acephate"
  100 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Acephate 0.1 mg/kg"
membership alachlor = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Alachlor"
  50 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Alachlor 0.05 mg/kg"
membership aldrinDieldrinSum = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Aldrin and dieldrin (sum of)"
  50 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Aldrin and dieldrin sum 0.05 mg/kg"
membership chlorpyriphosEthyl = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Chlorpyriphos-ethyl"
  200 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Chlorpyriphos-ethyl 0.2 mg/kg"
membership chlorpyriphosMethyl = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Chlorpyriphos-methyl"
  100 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Chlorpyriphos-methyl 0.1 mg/kg"
membership ddtSum = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "DDT (sum of specified DDE/DDT/TDE isomers)"
  1000 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: DDT sum 1 mg/kg"
membership deltamethrin = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Deltamethrin"
  500 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Deltamethrin 0.5 mg/kg"
membership diazinon = phEurTableMembership
  phEur11_0Revision01_2022
  "European Pharmacopoeia 11.0; 01/2022:20813 Pesticide residues"
  "Table 2.8.13.-1"
  "Diazinon"
  500 refl
  "Ph Eur 11.0, chapter 2.8.13, Table 2.8.13.-1: Diazinon 0.5 mg/kg"

------------------------------------------------------------------------
-- Australian incorporation route.
------------------------------------------------------------------------

record TGO93PhEurRoute : Set where
  constructor tgo93PhEurRoute
  field
    compilationReference : String
    scheduleReference : String
    parameterReference : String
    testMethodReference : String
    limitReference : String

open TGO93PhEurRoute public

canonicalTGO93PhEurRoute : TGO93PhEurRoute
canonicalTGO93PhEurRoute = tgo93PhEurRoute
  "TGO 93 F2022C01204, compilation 06 Dec 2022"
  "Schedule 1, specified tests, item 5"
  "Pesticides"
  "Ph Eur 2.8.13"
  "Not more than the limits specified in Ph Eur 2.8.13"

record AustralianPanelMembership (pesticide : NamedPesticide) : Set where
  constructor australianPanelMembership
  field
    tgoRoute : TGO93PhEurRoute
    phEurMembership : PhEurTableMembership pesticide
    interpretationBoundary : String

open AustralianPanelMembership public

australianMembership :
  (pesticide : NamedPesticide) → AustralianPanelMembership pesticide
australianMembership pesticide = australianPanelMembership
  canonicalTGO93PhEurRoute
  (membership pesticide)
  "Positive regulatory-table membership only; not proof of a laboratory's actual analyte scope, extraction recovery, LOD/LOQ, detection or batch compliance."

-- Requested positive examples: these are now proof-bearing source-bounded values.
ddtIsPresentInAustralianTGO93PhEurPanel : AustralianPanelMembership ddtSum
ddtIsPresentInAustralianTGO93PhEurPanel = australianMembership ddtSum

acephateIsPresentInAustralianTGO93PhEurPanel : AustralianPanelMembership acephate
acephateIsPresentInAustralianTGO93PhEurPanel = australianMembership acephate

chlorpyriphosEthylIsPresentInAustralianTGO93PhEurPanel :
  AustralianPanelMembership chlorpyriphosEthyl
chlorpyriphosEthylIsPresentInAustralianTGO93PhEurPanel =
  australianMembership chlorpyriphosEthyl

------------------------------------------------------------------------
-- Critical correction to a naive fixed-blacklist model.
--
-- Ph Eur 2.8.13 states that suspected pesticides not in Table 2.8.13.-1 are
-- routed to limits cross-referenced by Regulation (EC) No 396/2005; when they
-- are absent from both the table and EU texts, a calculated ADI-based limit is
-- used.  Therefore `not explicit table member` is not the same proposition as
-- `no regulatory limit route`.
------------------------------------------------------------------------

data RegulatoryLimitRoute : Set where
  explicitPhEurTable
  eu396CrossReference
  calculatedADILimit
  : RegulatoryLimitRoute

record PesticideMembershipBoundary : Set where
  constructor pesticideMembershipBoundary
  field
    namedRealPesticidesHavePositiveTableReceipts : Bool
    tgo93ReferencesPhEur2813 : Bool
    explicitTableMembershipEqualsActualLabAssayScope : Bool
    notExplicitlyListedMeansNoRegulatoryLimitRoute : Bool
    tableLimitEqualsInstrumentLOD : Bool
    tableLimitEqualsInstrumentLOQ : Bool

canonicalPesticideMembershipBoundary : PesticideMembershipBoundary
canonicalPesticideMembershipBoundary =
  pesticideMembershipBoundary true true false false false false
