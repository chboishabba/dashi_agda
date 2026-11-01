module DASHI.Culture.MissingDeceasedTwentyScientistRound26PrimaryLocatorPredecessorControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 26: PRIMARY-LOCATOR / PREDECESSOR-PROGRAMME CONTROL
--
-- Search produced two different kinds of progress that must not be collapsed:
-- (1) an exact locator for a primary source whose bytes are not yet in local
--     custody; and
-- (2) a directly readable primary predecessor-programme final report.
--
-- A locator is not byte custody.  A predecessor programme is not a successor
-- programme membership receipt.  An exact named object is not a cross-person
-- same-object edge unless the source literally pays that semantics.
------------------------------------------------------------------------

record SourcePaymentSurface : Set where
  constructor source-payment-surface
  field
    label : String
    source : Attribution.AttributedSource
    primaryLocatorPaid : Bool
    primaryBytesCustodyPaid : Bool
    objectIdentityPaid : Bool
    crossPersonIdentityPaid : Bool
    sameObjectSemanticsPaid : Bool
    temporalScopePaid : Bool
    operationalReceiptPaid : Bool
    pays : String
    doesNotPay : String

open SourcePaymentSurface public

armyFY2001Source : Attribution.AttributedSource
armyFY2001Source = Attribution.mkNoDOISource
  "U.S. Department of Defense"
  "Annual Report on Cooperative Agreements and Other Transactions Entered into During FY2001 Under 10 USC 2371"
  "Department of Defense report to Congress; archived official document locator"
  "2001"
  "https://web.archive.org/web/20210801183915/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
  Attribution.governmentSource
  "primary-source locator for DAAH01-01-9-R001; locator identity is paid but the legacy DOC bytes were not acquired in this pass"
  Attribution.publicAttribution

armyFY2001Snowball : Snowball.SourceRoleSnowballReceipt armyFY2001Source
armyFY2001Snowball = Snowball.canonicalSourceRoleSnowballReceipt armyFY2001Source

armyFY2001Surface : SourcePaymentSurface
armyFY2001Surface = source-payment-surface
  "Army FY2001 DAAH01-01-9-R001 report"
  armyFY2001Source
  true false true false false true false
  "exact archived official report locator, agreement identifier, Army AMCOM object identity and scheduled award dates"
  "local byte custody, second retained scientist, literal same-object role, completion/result, H2, H3 or targeting"

nasaNCC8124Source : Attribution.AttributedSource
nasaNCC8124Source = Attribution.mkNoDOISource
  "Ning Li"
  "Cooperative Agreement NCC8-124 Between NASA/MSFC and UAH Final Report"
  "NASA Technical Reports Server, document 20000038203"
  "2000"
  "https://ntrs.nasa.gov/api/citations/20000038203/downloads/20000038203.pdf?attachment=true"
  Attribution.governmentSource
  "primary directly readable final report for the separate 1996-2000 NASA/MSFC-UAH predecessor programme; retained as a negative control against silently inheriting Army membership or outcome"
  Attribution.publicAttribution

nasaNCC8124Snowball : Snowball.SourceRoleSnowballReceipt nasaNCC8124Source
nasaNCC8124Snowball = Snowball.canonicalSourceRoleSnowballReceipt nasaNCC8124Source

nasaNCC8124Surface : SourcePaymentSurface
nasaNCC8124Surface = source-payment-surface
  "NASA/MSFC-UAH NCC8-124 predecessor programme"
  nasaNCC8124Source
  true true true false false true false
  "primary report custody, programme dates, UAH/MSFC task split, superconducting-disk apparatus identity, and final-status boundary"
  "DAAH01-01-9-R001 outcome, Army successor membership, a second retained scientist, H2, H3, or operational linkage"

samMondaloySource : Attribution.AttributedSource
samMondaloySource = Attribution.mkNoDOISource
  "U.S. Department of the Air Force"
  "M200 Billets - FA930020P5032"
  "SAM.gov contract opportunity"
  "2020"
  "https://sam.gov/opp/4f451a2f4b6a4d948c9b183125895f32/view"
  Attribution.governmentSource
  "primary procurement surface paying 2020 AFRL/RQRE custody of a Mondaloy 200 billet object only"
  Attribution.publicAttribution

samMondaloySnowball : Snowball.SourceRoleSnowballReceipt samMondaloySource
samMondaloySnowball = Snowball.canonicalSourceRoleSnowballReceipt samMondaloySource

samMondaloySurface : SourcePaymentSurface
samMondaloySurface = source-payment-surface
  "2020 AFRL/RQRE Mondaloy procurement"
  samMondaloySource
  true true true false false true false
  "later AFRL/RQRE Mondaloy object persistence and 2020 procurement identity"
  "pre-2013 McCasland role, Reza-McCasland same-object semantics, temporal overlap, H2 or targeting"

hardwickUNSWSource : Attribution.AttributedSource
hardwickUNSWSource = Attribution.mkNoDOISource
  "UNSW Sydney"
  "Dallis Hardwick"
  "UNSW Science alumni career story"
  "2024"
  "https://www.unsw.edu.au/science/engage-with-us/alumni/alumni-career-stories/dallis-hardwick"
  Attribution.institutionalSource
  "independent institutional biography paying Jacinto/Hardwick Mondaloy co-development and Hardwick's later AFRL materials leadership; does not name McCasland on the object"
  Attribution.publicAttribution

hardwickUNSWSnowball : Snowball.SourceRoleSnowballReceipt hardwickUNSWSource
hardwickUNSWSnowball = Snowball.canonicalSourceRoleSnowballReceipt hardwickUNSWSource

hardwickUNSWSurface : SourcePaymentSurface
hardwickUNSWSurface = source-payment-surface
  "Jacinto/Hardwick invention lineage and later AFRL career"
  hardwickUNSWSource
  true true true true false true false
  "Jacinto-Hardwick co-invention lineage and Hardwick's later AFRL role"
  "McCasland participation in Mondaloy, one shared Reza-McCasland work package, H2 or operational linkage"

jplMaiwaldSURPSource : Attribution.AttributedSource
jplMaiwaldSURPSource = Attribution.mkNoDOISource
  "NASA Jet Propulsion Laboratory"
  "FY23 Strategic University Research Partnership: Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "JPL SURP poster SP23012 / CL#23-5018"
  "2023"
  "https://www.jpl.nasa.gov/site/research/media/posters/2023/SP23012p.pdf"
  Attribution.institutionalSource
  "exact Maiwald programme-object/team receipt; searched as a Hicks/Maiwald discriminator and does not name Hicks"
  Attribution.publicAttribution

jplMaiwaldSURPSnowball : Snowball.SourceRoleSnowballReceipt jplMaiwaldSURPSource
jplMaiwaldSURPSnowball = Snowball.canonicalSourceRoleSnowballReceipt jplMaiwaldSURPSource

jplMaiwaldSURPSurface : SourcePaymentSurface
jplMaiwaldSURPSurface = source-payment-surface
  "Maiwald SURP SP23012"
  jplMaiwaldSURPSource
  true true true true false true false
  "exact 2023 Maiwald PI object, co-investigator team, apparatus scope and poster identity"
  "Hicks participation, Hicks-Maiwald shared work package, H2 or operational linkage"

round26Sources : List SourcePaymentSurface
round26Sources =
  armyFY2001Surface ∷ nasaNCC8124Surface ∷ samMondaloySurface ∷ hardwickUNSWSurface ∷ jplMaiwaldSURPSurface ∷ []

round26SourceCount : Nat
round26SourceCount = 5

armyFY2001LocatorPaid : Bool
armyFY2001LocatorPaid = true

armyFY2001BytesCustodyPaid : Bool
armyFY2001BytesCustodyPaid = false

nasaNCC8124PrimaryBytesPaid : Bool
nasaNCC8124PrimaryBytesPaid = true

nasaPredecessorCannotPayArmySameProgramme : Bool
nasaPredecessorCannotPayArmySameProgramme = true

locatorCannotPayBytesCustody : Bool
locatorCannotPayBytesCustody = true

predecessorObjectCannotPaySuccessorMembership : Bool
predecessorObjectCannotPaySuccessorMembership = true

institutionalLineageCannotPayNamedRole : Bool
institutionalLineageCannotPayNamedRole = true

laterProcurementCannotPayEarlierRole : Bool
laterProcurementCannotPayEarlierRole = true

armySecondRetainedPersonLocated : Bool
armySecondRetainedPersonLocated = false

rezaMcCaslandSameObjectLocated : Bool
rezaMcCaslandSameObjectLocated = false

jplSharedWorkPackageLocated : Bool
jplSharedWorkPackageLocated = false

nudtSharedTaskLocated : Bool
nudtSharedTaskLocated = false

round26H2PaidCount : Nat
round26H2PaidCount = 0

round26H3PaidCount : Nat
round26H3PaidCount = 0

round26Pareto : String
round26Pareto = "Ning: primary Army locator is paid, but acquire the FY2001 DOC/SOW/closeout bytes and enumerate named people/apparatus. Reza/McCasland: Jacinto-Hardwick invention lineage plus later AFRL custody are paid, but a pre-2013 document naming McCasland on the Mondaloy object is still absent. JPL: Maiwald SP23012 is an exact object and does not pay Hicks participation; continue exact mission/instrument/work-package search. NUDT remains exact-task/code acquisition. Do not let a predecessor programme, institutional lineage, later procurement, or primary locator skip literal same-object semantics."