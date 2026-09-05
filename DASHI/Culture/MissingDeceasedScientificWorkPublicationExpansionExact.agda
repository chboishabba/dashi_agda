module DASHI.Culture.MissingDeceasedScientificWorkPublicationExpansionExact where

open import DASHI.Core.Prelude
import DASHI.Core.ScientificWorkAttributionExact as A
import DASHI.Core.ScientificSourceCitationExact as C

------------------------------------------------------------------------
-- PUBLICATION-LEVEL EXPANSION
-- Adds exact work receipts discovered after the first roster atlas.
------------------------------------------------------------------------

mccaslandThesisAttribution : A.ScientificWorkAttribution
mccaslandThesisAttribution = A.scientific-work-attribution
  "William Neil McCasland"
  "Sensor and Actuator Selection for Fault-Tolerant Control of Flexible Structures"
  "MIT Department of Aeronautics and Astronautics / AFIT / Draper Laboratory"
  A.namedAuthor
  A.primaryPublicationRecord
  "AD-A217384; AFIT/CI/CIA-88-227; CSDL-T-1010; NASA N90-20433; Hertz Thesis Prize 1989"
  "McCasland is the thesis author; work concerns sensor/actuator placement, controllability/observability and failure-tolerant reconfiguration for flexible structures."
  A.externalSourceOwner

mccaslandACCAttribution : A.ScientificWorkAttribution
mccaslandACCAttribution = A.scientific-work-attribution
  "William N. McCasland"
  "Fault-Tolerant Sensor and Actuator Selection for Control of Flexible Structures"
  "1989 American Control Conference"
  A.namedAuthor
  A.primaryPublicationRecord
  "ACC 1989 Vol. 2 pp. 1111-1116; NASA index A89-54007"
  "Conference paper by McCasland; uses controllability/observability Gramian norms as placement measures and demonstrates algorithms on flexible-structure examples."
  A.externalSourceOwner

chavezSpectrometerAttribution : A.ScientificWorkAttribution
chavezSpectrometerAttribution = A.scientific-work-attribution
  "Mark Anthony Chavez"
  "Calibration of two compact permanent magnet spectrometers for high current electron linear induction accelerators"
  "Los Alamos National Laboratory / Review of Scientific Instruments"
  A.namedAuthor
  A.primaryPublicationRecord
  "DOI 10.1063/1.5029837; LA-UR-18-21951"
  "LANL publication record lists Mark Anthony Chavez as coauthor. This identity remains separate from any broader Anthony-Chavez same-object question unless independently welded."
  A.externalSourceOwner

maiwaldQITAttribution : A.ScientificWorkAttribution
maiwaldQITAttribution = A.scientific-work-attribution
  "Frank Maiwald"
  "Sampling Accelerated Micron Scale Ice Particles with a Quadrupole Ion Trap Mass Spectrometer"
  "NASA JPL / Journal of the American Society for Mass Spectrometry"
  A.namedAuthor
  A.primaryPublicationRecord
  "DOI 10.1021/jasms.0c00442; PMID 33792296"
  "Publication lists Frank Maiwald as JPL coauthor on planetary ice-particle sampling with QIT mass spectrometry."
  A.externalSourceOwner

hicksHyakutakeAttribution : A.ScientificWorkAttribution
hicksHyakutakeAttribution = A.scientific-work-attribution
  "Michael D. Hicks"
  "Spectrophotometry and the Development of Emissions for C/1996 B2 (Comet Hyakutake)"
  "Icarus 127(2), 307-318"
  A.namedAuthor
  A.primaryPublicationRecord
  "DOI 10.1006/icar.1997.5697"
  "Hicks is named coauthor with Uwe Fink on publication-level comet spectrophotometry."
  A.externalSourceOwner

hicksNEATAttribution : A.ScientificWorkAttribution
hicksNEATAttribution = A.scientific-work-attribution
  "Michael D. Hicks"
  "Near-Nucleus Photometry of Comets Using Archived NEAT Data"
  "Icarus 188 (2007)"
  A.namedAuthor
  A.primaryPublicationRecord
  "JPL publication listing: Hicks, Bambery, Lawrence, Kollipara; Icarus 188, 457 (2007)"
  "Publication-level attribution to archived NEAT comet photometry."
  A.externalSourceOwner

------------------------------------------------------------------------
-- Citation registry.
------------------------------------------------------------------------

mccaslandThesisCitation : C.ScientificCitation
mccaslandThesisCitation = C.scientific-citation
  "William Neil McCasland"
  "Sensor and Actuator Selection for Fault-Tolerant Control of Flexible Structures"
  "Massachusetts Institute of Technology / AFIT / Charles Stark Draper Laboratory"
  1989
  (C.canonicalURL "https://ntrs.nasa.gov/citations/19910018877")
  "NASA technical-index entry N90-20433; AD-A217384; 194 p"
  C.authorshipSource
  "NASA index identifies McCasland as thesis author and summarises the fault-tolerant flexible-structure control problem."

mccaslandThesisWithCitation : C.AttributionWithCitation
mccaslandThesisWithCitation = C.attribution-with-citation mccaslandThesisAttribution mccaslandThesisCitation

chavezSpectrometerCitation : C.ScientificCitation
chavezSpectrometerCitation = C.scientific-citation
  "Trevor J. Burris-Mog; Mark Anthony Chavez; Michelle A. Espy; David C. Moir; Josef B. Schillig; Petr L. Volegov; Manuel J. Manard; Clifford P. Trainham"
  "Calibration of two compact permanent magnet spectrometers for high current electron linear induction accelerators"
  "Review of Scientific Instruments 89(7), 073303"
  2018
  (C.doi "10.1063/1.5029837")
  "LANL repository; LA-UR-18-21951"
  C.authorshipSource
  "LANL publication record lists Mark Anthony Chavez among the authors."

chavezSpectrometerWithCitation : C.AttributionWithCitation
chavezSpectrometerWithCitation = C.attribution-with-citation chavezSpectrometerAttribution chavezSpectrometerCitation

maiwaldQITCitation : C.ScientificCitation
maiwaldQITCitation = C.scientific-citation
  "Anton Belousov; Morgan Miller; Robert Continetti; Stojan Madzunkov; Jurij Simcic; Dragan Nikolic; Frank Maiwald; Sarah Waller; Michael Malaska; Morgan Cable"
  "Sampling Accelerated Micron Scale Ice Particles with a Quadrupole Ion Trap Mass Spectrometer"
  "Journal of the American Society for Mass Spectrometry"
  2021
  (C.doi "10.1021/jasms.0c00442")
  "PMID 33792296"
  C.authorshipSource
  "Publication names Frank Maiwald as JPL coauthor."

maiwaldQITWithCitation : C.AttributionWithCitation
maiwaldQITWithCitation = C.attribution-with-citation maiwaldQITAttribution maiwaldQITCitation

hicksHyakutakeCitation : C.ScientificCitation
hicksHyakutakeCitation = C.scientific-citation
  "Michael D. Hicks; Uwe Fink"
  "Spectrophotometry and the Development of Emissions for C/1996 B2 (Comet Hyakutake)"
  "Icarus 127(2), 307-318"
  1997
  (C.doi "10.1006/icar.1997.5697")
  "Icarus DOI record"
  C.authorshipSource
  "Publication-level Hicks comet-spectrophotometry receipt."

hicksHyakutakeWithCitation : C.AttributionWithCitation
hicksHyakutakeWithCitation = C.attribution-with-citation hicksHyakutakeAttribution hicksHyakutakeCitation

record PublicationExpansionBoundary : Set where
  constructor publication-expansion-boundary
  field
    technicalRoleMayBeUpgradedWhenNamedPublicationLocated : Bool
    technicalRoleMayBeUpgradedWhenNamedPublicationLocatedIsTrue :
      technicalRoleMayBeUpgradedWhenNamedPublicationLocated ≡ true
    similarNamePublicationAutomaticallyWeldsPersonIdentity : Bool
    similarNamePublicationAutomaticallyWeldsPersonIdentityIsFalse :
      similarNamePublicationAutomaticallyWeldsPersonIdentity ≡ false
    publicationAuthorshipImpliesSoleScientificOwnership : Bool
    publicationAuthorshipImpliesSoleScientificOwnershipIsFalse :
      publicationAuthorshipImpliesSoleScientificOwnership ≡ false

canonicalPublicationExpansionBoundary : PublicationExpansionBoundary
canonicalPublicationExpansionBoundary = publication-expansion-boundary true refl false refl false refl
