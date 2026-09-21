module DASHI.Physics.Foundations.RFMutualCouplingSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- MUTUAL-COUPLING / ACTIVE-REFLECTION / EMBEDDED-ELEMENT SOURCE ATLAS
--
-- Sources pay only bounded RF relationships.  They do not identify exact
-- hardware, exact emitter state, operational tasking, or authorization.
------------------------------------------------------------------------

nalumakkalActiveArrayPrimary : Source.AttributedSource
nalumakkalActiveArrayPrimary = Source.mkDOISource
  "Priya Suresh Nalumakkal; K. Maheshwara Reddy; K. J. Vinoy; Saurabh Shukla"
  "Wideband stripline fed tapered slot antenna with integral coupler for wide scan angle active phased array"
  "IET Microwaves, Antennas & Propagation 12(9), 1487-1493"
  "2018"
  "10.1049/iet-map.2017.0784"
  "https://doi.org/10.1049/iet-map.2017.0784"
  Source.academicArticleSource
  "primary experimental source paying the bounded claim that mutual coupling between array elements can be measured as S-parameters and used to compute an active reflection coefficient for an excited phased array"
  Source.publicAttribution

wangMutualCouplingPrimary : Source.AttributedSource
wangMutualCouplingPrimary = Source.mkDOISource
  "Zhi Ning Chen and coauthors"
  "Bandwidth Enhancement of Antenna Arrays Utilizing Mutual Coupling between Antenna Elements"
  "International Journal of Antennas and Propagation"
  "2010"
  "10.1155/2010/690713"
  "https://doi.org/10.1155/2010/690713"
  Source.academicArticleSource
  "primary source paying the bounded relationship among passive reflection coefficients, mutual-coupling S-parameters and active reflection coefficient in array analysis"
  Source.publicAttribution

mathworksEmbeddedElementReference : Source.AttributedSource
mathworksEmbeddedElementReference = Source.mkNoDOISource
  "MathWorks"
  "Verification of Far-Field Array Pattern Using Superposition with Embedded Element Patterns"
  "Antenna Toolbox documentation"
  "2026 snapshot"
  "https://www.mathworks.com/help/antenna/ug/verification-of-far-field-array-pattern-using-superposition-with-embedded-element-patterns.html"
  Source.practitionerSource
  "practitioner reference paying the bounded claim that an embedded-element pattern incorporates neighboring-element coupling and that superposition of embedded complex fields can reconstruct the fully excited array pattern"
  Source.publicAttribution

rfMutualCouplingAtlas : Source.AttributedSourceAtlas
rfMutualCouplingAtlas = Source.mkSourceAtlas
  "RF mutual-coupling / active-response source atlas"
  "DASHI.Physics.Foundations.RFMutualCouplingSourceAtlasExact"
  (nalumakkalActiveArrayPrimary ∷ wangMutualCouplingPrimary ∷ mathworksEmbeddedElementReference ∷ [])
  "sources pay bounded coupling, active-reflection and embedded-element relationships only; exact array identity, bearing recovery, deployment geometry and operational authority remain separate"
