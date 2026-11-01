module DASHI.Culture.MissingDeceasedTwentyScientistRound76POAMSFundingIdentifierWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact as R75

------------------------------------------------------------------------
-- ROUND 76: POAMS FUNDING-IDENTIFIER WELD
--
-- NTRS metadata for TM 20205010911 carries funding number
-- MSFC-RMB-QUANTUM-SAA8-1519855-1.  NASA's active-SAA register separately
-- lists SAA8-1519855.1 as "Advanced Propulsion Theory and Experimentation
-- POAMS Familiarization".  The shared agreement stem and POAMS context pay a
-- same-agreement-family weld.  Punctuation/format normalization alone does not
-- establish every internal amendment, task-order or revision identity.
------------------------------------------------------------------------

ntrsPOAMSTechnicalMemorandum : Attribution.AttributedSource
ntrsPOAMSTechnicalMemorandum = Attribution.mkNoDOISource
  "R.H. Eskridge; M.A. Nelson; M.P. Schoenfeld"
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "NASA Technical Reports Server / NASA Technical Memorandum 20205010911 / M-1531"
  "2021"
  "https://ntrs.nasa.gov/citations/20205010911"
  Attribution.governmentSource
  "Pays the exact TM metadata, MSFC acquisition source, Quantum Machines Space Act context and funding number MSFC-RMB-QUANTUM-SAA8-1519855-1; does not identify Amy Eskridge or The Institute as authors, counterparties or release recipients."
  Attribution.publicAttribution

ntrsFundingIdentifier : String
ntrsFundingIdentifier = "MSFC-RMB-QUANTUM-SAA8-1519855-1"

nasaRegisterSubagreementIdentifier : String
nasaRegisterSubagreementIdentifier = "SAA8-1519855.1"

fundingIdentifierAgreementFamilyWeldPaid : Bool
fundingIdentifierAgreementFamilyWeldPaid = true

sharedAgreementStemPaid : Bool
sharedAgreementStemPaid = true

poamsContextMatchesSubagreementTitlePaid : Bool
poamsContextMatchesSubagreementTitlePaid = true

tmInstitutionalObjectStrengthened : Bool
tmInstitutionalObjectStrengthened = true

formatNormalizationDoesNotPayInternalRevisionIdentity : Bool
formatNormalizationDoesNotPayInternalRevisionIdentity = true

fundingIdentifierDoesNotIdentifyAmy : Bool
fundingIdentifierDoesNotIdentifyAmy = true

fundingIdentifierDoesNotIdentifyTheInstitute : Bool
fundingIdentifierDoesNotIdentifyTheInstitute = true

amyInstituteIdentityStillUnpaid : Bool
amyInstituteIdentityStillUnpaid = true

samePaperIdentityStillUnpaid : Bool
samePaperIdentityStillUnpaid = true

round76H2PaidCount : Nat
round76H2PaidCount = 0

round76H3PaidCount : Nat
round76H3PaidCount = 0

round76Reading : String
round76Reading = "NASA NTRS metadata for TM 20205010911 records funding number MSFC-RMB-QUANTUM-SAA8-1519855-1. NASA's 2016 active Space Act Agreement register lists SAA8-1519855.1 as the Quantum Machines LLC 'Advanced Propulsion Theory and Experimentation POAMS Familiarization' agreement. The shared agreement stem plus exact POAMS context materially strengthens the weld between the later Technical Memorandum and the POAMS Space Act agreement family. The formalisation does not infer undocumented amendment/revision equivalence from punctuation normalization, and it still does not identify Amy Eskridge or The Institute on the institutional carrier."
