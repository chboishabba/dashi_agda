module DASHI.Physics.Foundations.RFComplexSmithSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- RF COMPLEX / SMITH-CHART SOURCE ATLAS
--
-- These sources pay only notation, impedance, reflection-coefficient,
-- S-parameter and Smith-chart relationships.  They do not make claims about
-- exact hardware provenance, emitter identity, operational tasking, or the
-- modular j-invariant.
------------------------------------------------------------------------

engineeringJNotationSource : Source.AttributedSource
engineeringJNotationSource = Source.mkNoDOISource
  "University of Victoria electrical/computer engineering course material"
  "Complex Numbers — i vs. j"
  "ECE course notes"
  "course-note snapshot"
  "https://www.ece.uvic.ca/~fayez/courses/310/resources/MITcomplex_numbers.pdf"
  Source.institutionalSource
  "source for the electrical-engineering convention j = sqrt(-1), used instead of i where i denotes current; pays notation only"
  Source.publicAttribution

keysightSmithChartSource : Source.AttributedSource
keysightSmithChartSource = Source.mkNoDOISource
  "Keysight Technologies"
  "Network Analysis Basics / Smith Chart review"
  "Keysight application note 5965-7707"
  "current hosted revision"
  "https://www.keysight.com/us/en/assets/7018-06841/application-notes/5965-7707.pdf"
  Source.practitionerSource
  "technical source for Z = R + jX, complex reflection coefficient, normalized impedance and the Smith chart as the mapping of the positive-real impedance half-plane into the reflection-coefficient disk"
  Source.publicAttribution

rohdeSmithChartSource : Source.AttributedSource
rohdeSmithChartSource = Source.mkNoDOISource
  "Rohde & Schwarz"
  "Understanding the Smith chart"
  "R&S Essentials"
  "2026 snapshot"
  "https://www.rohde-schwarz.com/uk/products/test-and-measurement/essentials-test-equipment/spectrum-analyzers/understanding-the-smith-chart_257989.html"
  Source.practitionerSource
  "technical source for normalized complex impedance, resistance circles, reactance arcs and Smith-chart reflection-coefficient visualization"
  Source.publicAttribution

rohdeSParameterSource : Source.AttributedSource
rohdeSParameterSource = Source.mkNoDOISource
  "Rohde & Schwarz"
  "Understanding S-parameters"
  "R&S Essentials"
  "2026 snapshot"
  "https://www.rohde-schwarz.com/au/products/test-and-measurement/essentials-test-equipment/spectrum-analyzers/understanding-s-parameters_257831.html"
  Source.practitionerSource
  "technical source for S-parameters as complex magnitude/phase observations of RF ports and for Smith-chart visualization of reflection parameters"
  Source.publicAttribution

rfComplexSmithAtlas : Source.AttributedSourceAtlas
rfComplexSmithAtlas = Source.mkSourceAtlas
  "electrical-engineering j / RF phasor / Smith-chart source atlas"
  "DASHI.Physics.Foundations.RFComplexSmithSourceAtlasExact"
  (engineeringJNotationSource ∷ keysightSmithChartSource ∷ rohdeSmithChartSource ∷ rohdeSParameterSource ∷ [])
  "sources pay notation and bounded RF coordinate relationships only; modular j-invariant identity, array hardware identity, exact emitter recovery and operational authority remain separate"
