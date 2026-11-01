module DASHI.Culture.MissingDeceasedTwentyScientistRound25AcquisitionResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
import DASHI.Culture.MissingDeceasedTwentyScientistRound24ProgrammeBridgeCandidatesExact as R24

------------------------------------------------------------------------
-- ROUND 25: ACQUISITION RESOLUTION
--
-- Round 24 records attractive programme-bridge candidates.  This layer makes
-- promotion eligibility executable without letting a source hit, a named pair,
-- or a plausible object silently become H2.  H2 requires three independent
-- payments on the candidate: primary custody, cross-person identity, and
-- literal same-object semantics.  H3 additionally requires pre-event temporal
-- overlap and an operational/security/custody receipt.
------------------------------------------------------------------------

infixr 6 _&&_
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

record AcquisitionResolution : Set where
  constructor acquisition-resolution
  field
    candidate : R24.ProgrammeBridgeCandidate
    resolutionName : String
    primaryCustodyPaid : Bool
    crossPersonIdentityPaid : Bool
    sameObjectSemanticsPaid : Bool
    preEventTemporalOverlapPaid : Bool
    preEventOperationalReceiptPaid : Bool
    primaryCustodyReceipt : String
    crossPersonReceipt : String
    sameObjectReceipt : String
    temporalReceipt : String
    operationalReceipt : String
    nextLiteralAcquisition : String

open AcquisitionResolution public

h2Eligible : AcquisitionResolution → Bool
h2Eligible r = primaryCustodyPaid r && crossPersonIdentityPaid r && sameObjectSemanticsPaid r

h3Eligible : AcquisitionResolution → Bool
h3Eligible r = h2Eligible r && preEventTemporalOverlapPaid r && preEventOperationalReceiptPaid r

ningArmyResolution : AcquisitionResolution
ningArmyResolution = acquisition-resolution
  R24.ningArmyCandidate
  "Ning Li / AC Gravity / DAAH01-01-9-R001"
  false false false false false
  "secondary public reproductions expose the award row; original DoD annual-report/SOW/closeout custody remains unpaid"
  "no second retained scientist is named on the acquired Army surface"
  "no literal retained-person same-object role receipt"
  "award dates are visible in secondary reproduction, but no second retained person exists to pay pairwise overlap"
  "no pre-event common operational/security/custody receipt"
  "recover the primary FY2001 DoD row, SOW, personnel/subcontract/facility material and closeout; enumerate every named person and apparatus identifier"

amyNingResolution : AcquisitionResolution
amyNingResolution = acquisition-resolution
  R24.amyNingCandidate
  "Amy Eskridge -> Ning Li historical reference"
  true true false false false
  "Amy's retained 2018 HAL5 presentation is a literal attributable source surface"
  "Amy and Ning are both literally identified in the source relationship"
  "the source is a retrospective reference to Ning/Torr/AC Gravity, not a receipt placing Amy on the Army programme object"
  "retrospective reference does not establish Amy's contemporaneous participation in the 2001 Army object"
  "no common pre-event operational receipt"
  "recover Amy's own reviewed Institute/NASA technical or release object and inspect it for AC Gravity, DAAH01-01-9-R001, apparatus, contractor, facility or personnel identity"

rezaMcCaslandResolution : AcquisitionResolution
rezaMcCaslandResolution = acquisition-resolution
  R24.rezaMcCaslandCandidate
  "Reza / Mondaloy / McCasland"
  true true false false false
  "SAM.gov directly pays 2020 AFRL/RQRE custody of the Mondaloy 200 billet procurement object"
  "Reza and McCasland identities are independently resolved, but not on one role-level Mondaloy document"
  "later AFRL procurement plus earlier command chronology does not name McCasland on the Mondaloy work package"
  "2020 procurement post-dates McCasland's 2011-2013 AFRL command and cannot pay contemporaneous role overlap"
  "no shared pre-event operational/security/custody receipt"
  "recover a pre-2013 Mondaloy AFRL contract, programme review, briefing, approval or tasking record that names McCasland and the Reza/Hardwick object"

jplResolution : AcquisitionResolution
jplResolution = acquisition-resolution
  R24.jplCandidate
  "Hicks / Maiwald JPL work-package bridge"
  true true false false false
  "separate attributable JPL science-object surfaces are already retained"
  "both retained scientists are identified as JPL-associated persons"
  "no exact mission/instrument/procurement/work-package identifier has yet been paid as shared"
  "institutional-era overlap is insufficient without dates on a literal shared technical object"
  "no common pre-event operational/security/custody receipt"
  "recover one mission, instrument, facility, procurement or work-package identifier naming both retained people or their exact components"

nudtResolution : AcquisitionResolution
nudtResolution = acquisition-resolution
  R24.nudtCandidate
  "Chen / Feng / Zhang Daibing NUDT task bridge"
  true true false false false
  "separate attributable NUDT institutional and technical-object surfaces are retained"
  "the candidate retained people are individually identified"
  "no exact PLA/NUDT task, project, lab, codebase or work-package has been paid across two retained scientists"
  "shared institution does not establish task-time overlap"
  "no common pre-event operational/security/tasking receipt"
  "recover one exact PLA/NUDT task, project, laboratory, codebase or work-package identifier naming at least two retained scientists"

round25Resolutions : List AcquisitionResolution
round25Resolutions =
  ningArmyResolution ∷ amyNingResolution ∷ rezaMcCaslandResolution ∷ jplResolution ∷ nudtResolution ∷ []

round25ResolutionCount : Nat
round25ResolutionCount = 5

round25H2EligibleCount : Nat
round25H2EligibleCount = 0

round25H3EligibleCount : Nat
round25H3EligibleCount = 0

primaryCustodyAloneCannotPayH2 : Bool
primaryCustodyAloneCannotPayH2 = true

crossPersonIdentityAloneCannotPayH2 : Bool
crossPersonIdentityAloneCannotPayH2 = true

sameObjectSemanticsAloneCannotPayH2 : Bool
sameObjectSemanticsAloneCannotPayH2 = true

h2CannotPayH3WithoutTemporalAndOperationalReceipts : Bool
h2CannotPayH3WithoutTemporalAndOperationalReceipts = true

ningH2Blocked : Bool
ningH2Blocked = h2Eligible ningArmyResolution

amyNingH2Blocked : Bool
amyNingH2Blocked = h2Eligible amyNingResolution

rezaMcCaslandH2Blocked : Bool
rezaMcCaslandH2Blocked = h2Eligible rezaMcCaslandResolution

jplH2Blocked : Bool
jplH2Blocked = h2Eligible jplResolution

nudtH2Blocked : Bool
nudtH2Blocked = h2Eligible nudtResolution

round25Pareto : String
round25Pareto = "The live bottleneck is same-object semantics, not candidate generation. First acquire primary DAAH01-01-9-R001 custody and enumerate its people/object graph; in parallel recover a pre-2013 Mondaloy role/work-package receipt and Amy's own reviewed technical/release object. JPL and NUDT remain exact-work-package searches. Only a source that pays primary custody + cross-person identity + literal same-object semantics can make h2Eligible evaluate true."
