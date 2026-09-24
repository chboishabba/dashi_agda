module DASHI.Physics.Foundations.RFArrayManifoldSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ARRAY-MANIFOLD / BEAMFORMING / DOA SOURCE ATLAS
--
-- These sources pay only bounded relationships among antenna-array geometry,
-- steering/manifold coordinates, beamforming, and direction-of-arrival
-- estimation.  They do not identify exact hardware, emitter identity,
-- operational tasking, or authorize any action.
------------------------------------------------------------------------

godaraArrayReview : Source.AttributedSource
godaraArrayReview = Source.mkDOISource
  "Lal C. Godara"
  "Application of antenna arrays to mobile communications. II. Beam-forming and direction-of-arrival considerations"
  "Proceedings of the IEEE 85(8), 1195-1245"
  "1997"
  "10.1109/5.622504"
  "https://doi.org/10.1109/5.622504"
  Source.academicArticleSource
  "classic review source paying the bounded claim that antenna arrays support beamforming and direction-of-arrival estimation through spatially structured observations"
  Source.publicAttribution

belloniManifoldSeparation : Source.AttributedSource
belloniManifoldSeparation = Source.mkDOISource
  "Fabio Belloni; Andreas Richter; Visa Koivunen"
  "DoA Estimation Via Manifold Separation for Arbitrary Array Structures"
  "IEEE Transactions on Signal Processing 55(10), 4800-4810"
  "2007"
  "10.1109/TSP.2007.896115"
  "https://doi.org/10.1109/TSP.2007.896115"
  Source.academicArticleSource
  "primary source paying the bounded claim that an array steering/manifold model separates array-dependent structure from wavefield-dependent structure for DoA estimation"
  Source.publicAttribution

electromagneticManifoldPrimary : Source.AttributedSource
electromagneticManifoldPrimary = Source.mkDOISource
  "Miguel R. Castellanos; Robert W. Heath Jr."
  "Electromagnetic Manifold Characterization of Antenna Arrays"
  "IEEE Transactions on Wireless Communications 24(3), 1772-1785"
  "2025"
  "10.1109/TWC.2024.3503415"
  "https://doi.org/10.1109/TWC.2024.3503415"
  Source.academicArticleSource
  "primary source paying the bounded claim that realistic array manifolds can encode geometry and electromagnetic effects and be consumed by beamforming optimization"
  Source.publicAttribution

keysightPhasedArrayPrimer : Source.AttributedSource
keysightPhasedArrayPrimer = Source.mkNoDOISource
  "Keysight Technologies"
  "Designing Phased Arrays: Key Principles, Challenges, and Solutions"
  "Keysight technical article"
  "2026 snapshot"
  "https://www.keysight.com/blogs/en/tech/sim-des/designing-phased-arrays-key-principles-challenges-and-solutions"
  Source.practitionerSource
  "practitioner source paying the bounded engineering relationship that controlled element phase/delay relationships combine array signals and support beam steering/beamforming; not a proof of any exact formal array model"
  Source.publicAttribution

rfArrayManifoldAtlas : Source.AttributedSourceAtlas
rfArrayManifoldAtlas = Source.mkSourceAtlas
  "RF array-manifold / beamforming / DoA source atlas"
  "DASHI.Physics.Foundations.RFArrayManifoldSourceAtlasExact"
  (godaraArrayReview ∷ belloniManifoldSeparation ∷ electromagneticManifoldPrimary ∷ keysightPhasedArrayPrimer ∷ [])
  "sources pay bounded array-manifold, steering, beamforming and DoA relationships only; exact hardware identity, exact world recovery, deployment geometry and operational authority remain separate"
