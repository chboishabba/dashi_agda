module DASHI.Culture.MissingDeceasedTwentyScientistRound81LeBlancDOIGapComponentBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 81 / LEBLANC DOI GAP-ANALYSIS VS SAME-WBS COMPONENT BOUNDARY
--
-- Public source-bounded acquisition result.
--
-- Programme-level carrier:
--   N. Dianne Bull Ezell, Tyler Steiner, Joshua Leblanc, Jarvis Caffrey,
--   "Space Fission Instrumentation and Control Technology Gaps",
--   NPIC&HMIT 2025, American Nuclear Society, pp. 1694-1701,
--   DOI 10.13182/NPICHMIT25-46370.
--
-- Same-WBS component/testing carrier:
--   John D. Wrbanek, "Thin Film Sensors for Fission Surface Power",
--   NASA NTRS 20240010391, WBS 658133.04.01.22.01.06,
--   NASA Glenn inquiry on Sandia radiation-testing capabilities.
--
-- The exact WBS is a real programme-coordinate weld.  It does not imply that
-- every author on the programme-level gap paper worked on every thin-film
-- sensor component, nor does it create a second retained-scientist crossing.
------------------------------------------------------------------------

record SourceCarrier : Set where
  constructor sourceCarrier
  field
    authors : String
    title : String
    publication : String
    persistentIdentifier : String
    scope : String

open SourceCarrier public

programmeGapCarrier : SourceCarrier
programmeGapCarrier = sourceCarrier
  "N. Dianne Bull Ezell; Tyler Steiner; Joshua Leblanc; Jarvis Caffrey"
  "Space Fission Instrumentation and Control Technology Gaps"
  "Proceedings of NPIC&HMIT 2025, American Nuclear Society, pp. 1694-1701"
  "DOI:10.13182/NPICHMIT25-46370"
  "programme-level space-fission instrumentation-and-control technology-gap analysis"

componentTestingCarrier : SourceCarrier
componentTestingCarrier = sourceCarrier
  "John D. Wrbanek"
  "Thin Film Sensors for Fission Surface Power"
  "NASA Technical Reports Server, NTRS 20240010391"
  "WBS:658133.04.01.22.01.06"
  "component-level thin-film-sensor work presented for a NASA Glenn inquiry on Sandia radiation-testing capabilities"

leblancDevelopmentCarrier : SourceCarrier
leblancDevelopmentCarrier = sourceCarrier
  "Robert Okojie; Teresa Benko; Tyler Steiner; Kaiser Aguirre; Christopher Barth; Dianne Ezell; Angel Martinez-Sanchez; Robert Bruckner; Joshua Leblanc; Jarvis Caffrey"
  "NASA 40 kW Fission Surface Power I and C Technology Development Path"
  "NASA Technical Reports Server, NTRS 20250008475"
  "WBS:658133.04.01.22.01.06"
  "programme-development carrier naming Joshua Leblanc and the FICS executive structure"

programmeGapCarrierPaid : Bool
programmeGapCarrierPaid = true

sameWBSComponentCarrierPaid : Bool
sameWBSComponentCarrierPaid = true

sameWBSProgrammeCoordinatePaid : Bool
sameWBSProgrammeCoordinatePaid = true

sameWBSDoesNotPaySameComponentRole : Bool
sameWBSDoesNotPaySameComponentRole = true

programmePaperDoesNotPaySensorAuthorship : Bool
programmePaperDoesNotPaySensorAuthorship = true

sensorPresentationDoesNotPayLeBlancComponentRole : Bool
sensorPresentationDoesNotPayLeBlancComponentRole = true

secondRetainedScientistPaid : Bool
secondRetainedScientistPaid = false

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record Round81Boundary : Set where
  constructor round81Boundary
  field
    doiBearingGapAnalysisPaid : Bool
    exactWBSSameNeighbourhoodPaid : Bool
    sameWBSPromotesSameComponentRole : Bool
    secondRetainedCrossingPaid : Bool
    h2PromotionPaid : Bool
    h3PromotionPaid : Bool

canonicalRound81Boundary : Round81Boundary
canonicalRound81Boundary = round81Boundary
  true true false false false false
