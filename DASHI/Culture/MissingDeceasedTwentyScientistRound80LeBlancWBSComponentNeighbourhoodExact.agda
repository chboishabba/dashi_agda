module DASHI.Culture.MissingDeceasedTwentyScientistRound80LeBlancWBSComponentNeighbourhoodExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact as R40

------------------------------------------------------------------------
-- ROUND 80: LEBLANC FSP I&C WBS COMPONENT NEIGHBOURHOOD
--
-- Two public NASA NTRS carriers share exact WBS 658133.04.01.22.01.06:
--   * NASA 40 kW Fission Surface Power I&C Technology Development Path,
--     including Joshua LeBlanc.
--   * Thin Film Sensors for Fission Surface Power, John D. Wrbanek, tied to a
--     NASA Glenn inquiry on Sandia radiation-testing capabilities.
--
-- The shared WBS materially narrows the acquisition neighbourhood to a
-- component/testing branch inside FSP I&C.  It does not prove that every person
-- on one carrier worked on every component in the other carrier, and it does
-- not locate a second retained scientist on the searched same-WBS surfaces.
------------------------------------------------------------------------

leblancFSPICDevelopmentPath : Attribution.AttributedSource
leblancFSPICDevelopmentPath = Attribution.mkNoDOISource
  "Robert Okojie; Teresa Benko; Tyler Steiner; Kaiser Aguirre; Christopher Barth; N. Dianne Bull Ezell; Angel Martinez-Sanchez; Robert Bruckner; Joshua Leblanc; Jarvis Caffrey"
  "NASA 40 kW Fission Surface Power I&C Technology Development Path"
  "NASA Technical Reports Server / Fission Surface Power Technology Maturation Webinar Series"
  "2025"
  "https://ntrs.nasa.gov/citations/20250008475"
  Attribution.governmentSource
  "Pays Joshua LeBlanc on exact WBS 658133.04.01.22.01.06 and the public FSP I&C maturation carrier; does not assign him to every subordinate sensor/test activity."
  Attribution.publicAttribution

wrbanekThinFilmSensors : Attribution.AttributedSource
wrbanekThinFilmSensors = Attribution.mkNoDOISource
  "John D. Wrbanek"
  "Thin Film Sensors for Fission Surface Power"
  "NASA Technical Reports Server"
  "2024"
  "https://ntrs.nasa.gov/citations/20240010391"
  Attribution.governmentSource
  "Pays the same WBS 658133.04.01.22.01.06 on a thin-film-sensor FSP carrier and a NASA Glenn inquiry on Sandia radiation-testing capabilities; does not name Joshua LeBlanc on that component presentation."
  Attribution.publicAttribution

sameWBSExactKeyPaid : Bool
sameWBSExactKeyPaid = true

thinFilmSensorNeighbourhoodPaid : Bool
thinFilmSensorNeighbourhoodPaid = true

sandiaRadiationTestingNeighbourhoodPaid : Bool
sandiaRadiationTestingNeighbourhoodPaid = true

fspICComponentNeighbourhoodNarrowed : Bool
fspICComponentNeighbourhoodNarrowed = true

secondRetainedScientistOnWBSCarrierPaid : Bool
secondRetainedScientistOnWBSCarrierPaid = false

leblancNamedOnThinFilmSensorCarrierPaid : Bool
leblancNamedOnThinFilmSensorCarrierPaid = false

sameWBSDoesNotImplySameComponentRole : Bool
sameWBSDoesNotImplySameComponentRole = true

sameWBSDoesNotImplySameMeetingAttendance : Bool
sameWBSDoesNotImplySameMeetingAttendance = true

sameWBSDoesNotImplySameFacilityTask : Bool
sameWBSDoesNotImplySameFacilityTask = true

componentNeighbourhoodDoesNotPayCrossPersonObject : Bool
componentNeighbourhoodDoesNotPayCrossPersonObject = true

round80H2PaidCount : Nat
round80H2PaidCount = 0

round80H3PaidCount : Nat
round80H3PaidCount = 0

round80Reading : String
round80Reading = "Exact-key acquisition materially narrows Joshua LeBlanc's FSP I&C neighbourhood. NASA NTRS 20250008475 places LeBlanc on WBS 658133.04.01.22.01.06 for the 40 kW Fission Surface Power I&C technology-development path. NASA NTRS 20240010391 independently carries the same WBS for Thin Film Sensors for Fission Surface Power and ties that component branch to a NASA Glenn inquiry on Sandia radiation-testing capabilities. The shared WBS is a real programme-coordinate weld, but it does not place LeBlanc on the thin-film-sensor presentation, assign every WBS participant to every component, or locate a second retained scientist. H2 and H3 remain unpaid."
