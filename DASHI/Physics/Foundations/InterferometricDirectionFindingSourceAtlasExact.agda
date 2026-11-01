module DASHI.Physics.Foundations.InterferometricDirectionFindingSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Dedicated primary-source payment for the interferometric / phase-comparison
-- direction-finding leaf discovered by the RF acquisition snowball.
------------------------------------------------------------------------

phaseDifferenceAoAPrimary : Source.AttributedSource
phaseDifferenceAoAPrimary = Source.mkDOISource
  "J. P. Younger"
  "Interferometer angle-of-arrival determination using precalculated phases"
  "Radio Science 52"
  "2017"
  "10.1002/2017RS006284"
  "https://doi.org/10.1002/2017RS006284"
  Source.academicArticleSource
  "primary research source for the bounded relation that phase difference between receiving antennas can support angle-of-arrival inference, with ambiguity and geometry constraints retained"
  Source.publicAttribution

correlativeInterferometerDFPrimary : Source.AttributedSource
correlativeInterferometerDFPrimary = Source.mkDOISource
  "Minkyu Oh; Young-Seok Lee; In-Ki Lee; Bang Chul Jung"
  "Simultaneous Correlative Interferometer Technique for Direction Finding of Signal Sources"
  "Sensors 23(21):8938"
  "2023"
  "10.3390/s23218938"
  "https://doi.org/10.3390/s23218938"
  Source.academicArticleSource
  "primary research source for antenna-array direction finding using received-signal phase information and correlative interferometry; does not imply exact emitter identity or universal superiority over other DF methods"
  Source.publicAttribution

interferometricDirectionFindingAtlas : Source.AttributedSourceAtlas
interferometricDirectionFindingAtlas = Source.mkSourceAtlas
  "interferometric direction-finding primary-source atlas"
  "DASHI.Physics.Foundations.InterferometricDirectionFindingSourceAtlasExact"
  (phaseDifferenceAoAPrimary ∷ correlativeInterferometerDFPrimary ∷ [])
  "pays only bounded phase-difference / array-geometry / direction-of-arrival relationships; citation imports neither proof nor exact hardware identity nor operational authority"
