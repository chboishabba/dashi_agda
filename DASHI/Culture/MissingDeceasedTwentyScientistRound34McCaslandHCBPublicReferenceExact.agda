module DASHI.Culture.MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Culture.MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact as R32

------------------------------------------------------------------------
-- ROUND 34: MCCASLAND -> HCB PUBLIC PROGRAMME REFERENCE
--
-- AIAA's own SPACE 2013 recap pays McCasland's participation on the
-- "Aligning Technology Roadmaps to Support Space Goals" panel.  A
-- contemporaneous Space Review report from that conference attributes to
-- McCasland a discussion of AFRL's Hydrocarbon Boost work and RD-180 policy
-- dependence.  This upgrades the McCasland edge from command-window overlap to
-- a personal contemporaneous HCB programme reference.
--
-- It still does not make him a participant on FA9300-07-C-0001, a Mondaloy
-- materials task, Monica Jacinto's project team, or any specific HCB work
-- package.  Public programme reference and task-role identity remain distinct.
------------------------------------------------------------------------

record McCaslandHCBPublicReferenceReceipt : Set where
  constructor mccasland-hcb-public-reference-receipt
  field
    aiaaConferenceSource : Attribution.AttributedSource
    contemporaneousReportSource : Attribution.AttributedSource
    monicaHCBSource : Attribution.AttributedSource
    aiaaPanelParticipationPaid : Bool
    personalHCBReferencePaid : Bool
    rd180PolicyContextPaid : Bool
    formerAFRLCommanderIdentityPaid : Bool
    monicaHCBProjectRolePaid : Bool
    hcbTaskRolePaid : Bool
    hcbContractRolePaid : Bool
    mondaloyRolePaid : Bool
    crossPersonSameObjectPaid : Bool
    pays : String
    doesNotPay : String
    nextLiteralPayment : String

open McCaslandHCBPublicReferenceReceipt public

aiaaSpace2013Source : Attribution.AttributedSource
aiaaSpace2013Source = Attribution.mkNoDOISource
  "American Institute of Aeronautics and Astronautics"
  "Videos from AIAA SPACE 2013"
  "AIAA conference recap"
  "2013"
  "https://aiaa.org/2013/10/03/videos-from-space-now-available-space-2013-recap/"
  Attribution.institutionalSource
  "primary conference-organiser source paying Maj Gen Neil McCasland's participation as Past Commander, AFRL, on the 12-Sep-2013 Aligning Technology Roadmaps to Support Space Goals panel"
  Attribution.publicAttribution

aiaaSpace2013Snowball : Snowball.SourceRoleSnowballReceipt aiaaSpace2013Source
aiaaSpace2013Snowball = Snowball.canonicalSourceRoleSnowballReceipt aiaaSpace2013Source

spaceReview2013Source : Attribution.AttributedSource
spaceReview2013Source = Attribution.mkNoDOISource
  "Jeff Foust"
  "The case for kerolox"
  "The Space Review"
  "2013"
  "https://www.thespacereview.com/article/2384/1"
  Attribution.newsSource
  "contemporaneous conference reporting attributing to McCasland an explicit reference to AFRL Hydrocarbon Boost work and concern over U.S. dependence on the RD-180"
  Attribution.publicAttribution

spaceReview2013Snowball : Snowball.SourceRoleSnowballReceipt spaceReview2013Source
spaceReview2013Snowball = Snowball.canonicalSourceRoleSnowballReceipt spaceReview2013Source

round34Receipt : McCaslandHCBPublicReferenceReceipt
round34Receipt = mccasland-hcb-public-reference-receipt
  aiaaSpace2013Source
  spaceReview2013Source
  R32.engineersCouncilSource
  true
  true
  true
  true
  true
  false
  false
  false
  false
  "McCasland's personal participation on the AIAA SPACE 2013 roadmap panel and a contemporaneous attributed personal reference to AFRL's Hydrocarbon Boost work/RD-180 policy context; Monica's separate source-paid Mondaloy/HCB project role"
  "McCasland's role on FA9300-07-C-0001, a Mondaloy materials work package, attendance at the 18-Sep-2012 HCB industry day, a literal Monica-McCasland same-object receipt, H2, H3, targeting, suppression, or causal linkage"
  "recover an identity-bearing HCB source that moves from McCasland's public programme reference to a task/contract role: 2011-2013 contract modification, programme-review approval chain, industry-day attendee/distribution record, materials-tasking record, briefing signature, award-fee review, or JANNAF/NSMMS roster naming him on the same HCB/Mondaloy object"

aiaaPanelParticipationPaid : Bool
aiaaPanelParticipationPaid = true

personalHCBReferencePaid : Bool
personalHCBReferencePaid = true

rd180PolicyContextPaid : Bool
rd180PolicyContextPaid = true

hcbTaskRolePaid : Bool
hcbTaskRolePaid = false

hcbContractRolePaid : Bool
hcbContractRolePaid = false

mondaloyRolePaid : Bool
mondaloyRolePaid = false

crossPersonSameObjectPaid : Bool
crossPersonSameObjectPaid = false

publicProgrammeReferenceCannotPayTaskRole : Bool
publicProgrammeReferenceCannotPayTaskRole = true

conferencePanelCannotPayContractParticipation : Bool
conferencePanelCannotPayContractParticipation = true

policyReferenceCannotPayMaterialsRole : Bool
policyReferenceCannotPayMaterialsRole = true

round34H2PaidCount : Nat
round34H2PaidCount = 0

round34H3PaidCount : Nat
round34H3PaidCount = 0

round34Pareto : String
round34Pareto = "McCasland -> HCB has advanced from command-era overlap to a personal contemporaneous programme reference. Monica -> HCB/Mondaloy is already paid separately. The remaining H2 discriminator is now strictly task/contract role identity on the same object. Prioritise 18-Sep-2012 attendee/distribution records, FA9300-07-C-0001 modifications/reviews, and 2013 HCB materials proceedings/approval chains that literally name McCasland."