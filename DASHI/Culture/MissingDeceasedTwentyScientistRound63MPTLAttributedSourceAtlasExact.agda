module DASHI.Culture.MissingDeceasedTwentyScientistRound63MPTLAttributedSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ROUND 63: ATTRIBUTED MPTL SOURCE ATLAS
--
-- The live MPTL acquisition now uses the repository-wide attribution object:
-- author, exact title, publication context, year, DOI state, canonical URL,
-- source kind, and proposition-scoped formalisation relationship.
--
-- `noDOIRecordedByAtlas` is deliberately local: it means this atlas has not
-- acquired a DOI for that exact carrier. It does not prove that no DOI exists.
------------------------------------------------------------------------

schulzeAchromatSource : Source.AttributedSource
schulzeAchromatSource = Source.mkNoDOISource
  "Martin E. Schulze"
  "Achromat Design for Multi-Pulse Test Line"
  "Los Alamos National Laboratory report LA-UR-22-21508; OSTI public carrier"
  "2022"
  "https://www.osti.gov/servlets/purl/1846874"
  Source.governmentSource
  "Pays the exact DARHT-II MPTL 90-degree achromat design carrier: two 45-degree dipoles plus a focusing quadrupole. Does not by itself pay Alex Press participation, Chavez participation on this revision, or a retained-person crossing."
  Source.publicAttribution

brandesECRSource : Source.AttributedSource
brandesECRSource = Source.mkNoDOISource
  "Aaron Mills Brandes"
  "DARHT Multi-Pulse Test Line (MPTL) ECR"
  "Los Alamos National Laboratory report LA-UR-24-30822; Engineering Capability Review; OSTI public carrier"
  "2024"
  "https://www.osti.gov/servlets/purl/2460464"
  Source.governmentSource
  "Pays an exact MPTL Engineering Capability Review carrier and Brandes authorship. Does not identify a second retained scientist or transfer attendance/reviewer identity beyond what the public carrier states."
  Source.publicAttribution

chavezBPMSource : Source.AttributedSource
chavezBPMSource = Source.mkNoDOISource
  "Carl Ekdahl; Kimberly L. Abdallah; William B. Broste; M. Anthony Chavez; Christopher J. Mastrangelo; Matthew C. Richards"
  "An Improved Beam Position Monitor for Scorpius and the DARHT Multi-Pulse Test Line"
  "Los Alamos National Laboratory report LA-UR-24-27763; OSTI public carrier"
  "2024"
  "https://www.osti.gov/servlets/purl/2406682"
  Source.governmentSource
  "Pays Anthony Chavez on an exact Scorpius/DARHT MPTL beam-position-monitor technical carrier. The exact acquired author surface names no second retained scientist; that bounded observation does not establish global non-participation elsewhere."
  Source.publicAttribution

pressBrandesAchromatProceedingsSource : Source.AttributedSource
pressBrandesAchromatProceedingsSource = Source.mkNoDOISource
  "A. F. Press; A. M. Brandes; J. M. Campos; M. Schulze; M. A. Jaworski"
  "90-Degree Achromatic Bend for Transport of an Intense Electron Beam with Nominal Energy Spread of 16-17 MeV"
  "2025 IEEE Pulsed Power & Plasma Science (PPPS) conference proceedings"
  "2025"
  "https://www.proceedings.com/content/083/083021webtoc.pdf"
  Source.academicArticleSource
  "Pays a formal coauthored achromat publication linking Press, Brandes, Campos, Schulze and Jaworski on the 90-degree bend technical object. DOI remains unresolved in the acquired atlas and is not guessed."
  Source.publicAttribution

ipmhvcMPTLProgrammeSource : Source.AttributedSource
ipmhvcMPTLProgrammeSource = Source.mkNoDOISource
  "A. M. Brandes; M. Schulze; A. Press; J. Campos"
  "Multi-Pulse Test Line (MPTL)"
  "2024 IEEE International Power Modulator and High Voltage Conference programme, presentation P2-29"
  "2024"
  "https://www.ipmhvc.com/wp-content/uploads/2024/04/IPMHVC-2024-ConfTool-Schedule-With-Presentations-20240425.pdf"
  (Source.namedSourceKind "conference programme")
  "Pays literal co-naming of Brandes, Schulze, Press and Campos on one named MPTL presentation. Programme listing does not by itself prove content beyond title/authorship/affiliation."
  Source.publicAttribution

jglobalAchromatMirrorSource : Source.AttributedSource
jglobalAchromatMirrorSource = Source.mkNoDOISource
  "Japan Science and Technology Agency / J-GLOBAL bibliographic record"
  "90-Degree Achromatic Bend for Transport of an Intense Electron Beam with Nominal Energy Spread of 16-17 MeV"
  "J-GLOBAL ID 202602275966019137; reference number 26A0072248"
  "2026 record for 2025 publication"
  "https://jglobal.jst.go.jp/en/detail?JGLOBAL_ID=202602275966019137"
  Source.institutionalSource
  "Independent bibliographic indexing of title, authors, LANL affiliation, proceedings context and year. It is a metadata mirror, not an independent experimental replication and does not multiply proof of the underlying technical claim."
  Source.publicAttribution

pressJaworskiDARHTDOISource : Source.AttributedSource
pressJaworskiDARHTDOISource = Source.mkDOISource
  "A. F. Press; M. A. Jaworski; D. C. Moir; S. Szustkowski"
  "Experimental Verification of DARHT Axis 1 Injector PIC Simulations"
  "Proceedings of IPAC2022, JACoW"
  "2022"
  "10.18429/JACoW-IPAC2022-WEPOTK054"
  "https://doi.org/10.18429/JACoW-IPAC2022-WEPOTK054"
  Source.academicArticleSource
  "Pays a DOI-bearing DARHT technical-lineage carrier for Press and Jaworski. It is not an MPTL paper and cannot transfer its DOI, exact-object identity, or claim scope to the MPTL achromat carriers."
  Source.publicAttribution

mptlAttributedSourceAtlas : Source.AttributedSourceAtlas
mptlAttributedSourceAtlas = Source.mkSourceAtlas
  "DARHT MPTL exact-object attribution atlas"
  "DASHI.Culture.MissingDeceasedTwentyScientistRound63MPTLAttributedSourceAtlasExact"
  (schulzeAchromatSource ∷
   brandesECRSource ∷
   chavezBPMSource ∷
   pressBrandesAchromatProceedingsSource ∷
   ipmhvcMPTLProgrammeSource ∷
   jglobalAchromatMirrorSource ∷
   pressJaworskiDARHTDOISource ∷ [])
  "Exact MPTL/DARHT object carriers plus explicitly related DOI-bearing lineage and bibliographic mirrors. Every source relationship is proposition-scoped; citation imports neither proof nor authority."

mptlExactCarrierDOIUnresolvedIsAtlasLocal : Bool
mptlExactCarrierDOIUnresolvedIsAtlasLocal = true

relatedDOICannotTransferToMPTLClaim : Bool
relatedDOICannotTransferToMPTLClaim = true

bibliographicMirrorDoesNotMultiplyProof : Bool
bibliographicMirrorDoesNotMultiplyProof = true

reportNumberAndDOIAreDistinctIdentifierKinds : Bool
reportNumberAndDOIAreDistinctIdentifierKinds = true

missingDOICannotBeFilledFromTitleSimilarity : Bool
missingDOICannotBeFilledFromTitleSimilarity = true

sourceRelationshipCannotExceedCarrierText : Bool
sourceRelationshipCannotExceedCarrierText = true

round63H2PaidCount : Nat
round63H2PaidCount = 0

round63H3PaidCount : Nat
round63H3PaidCount = 0

round63Reading : String
round63Reading = "The live MPTL evidence family now uses AttributedSourceCore directly. LA-UR identifiers are retained as canonical report identifiers when no DOI has been acquired. The 2025 PPPS achromat paper remains DOI-unresolved in this atlas; that is an atlas-local state, not a universal no-DOI claim. Press/Jaworski IPAC2022 provides a real DOI-bearing DARHT lineage source, but its DOI and evidentiary scope cannot transfer to MPTL. J-GLOBAL is retained as an independent bibliographic metadata mirror, not independent experimental confirmation. H2/H3 remain unpaid."
