module DASHI.Physics.Foundations.SmithChartSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

phillipSmith1939 : Source.AttributedSource
phillipSmith1939 = Source.mkNoDOISource
  "Phillip H. Smith"
  "Transmission Line Calculator"
  "Electronics"
  "January 1939"
  "https://www.rfcafe.com/references/electronics-mag/transmission-line-calculator-phillip-h-smith-electronics-magazine-january-1939.htm"
  Source.archivalSource
  "primary historical source for Smith's transmission-line impedance coordinate calculator and normalized impedance geometry; citation does not identify the modular j-invariant with electrical-engineering j notation"
  Source.publicAttribution

phillipSmith1944 : Source.AttributedSource
phillipSmith1944 = Source.mkNoDOISource
  "Phillip H. Smith"
  "An Improved Transmission Line Calculator"
  "Electronics"
  "January 1944"
  "https://www.worldradiohistory.com/Archive-Electronics/40s/Electronics-1944-01.pdf"
  Source.archivalSource
  "primary historical source for the improved calculator including impedance/admittance and reflection-coefficient magnitude/angle scales"
  Source.publicAttribution
