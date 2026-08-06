module DASHI.Biology.ConsciousAccessRound3ExtendedSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound3SourceAtlas as Sources

------------------------------------------------------------------------
-- Additional provenance for the algorithmic-growth, IFS, integrated-growth,
-- and signed-distance tranches.

lindenmayerLSystemSource : Sources.SourceRecord
lindenmayerLSystemSource =
  Sources.sourceRecord
    "Aristid Lindenmayer"
    "Mathematical models for cellular interactions in development I. Filaments with one-sided inputs"
    "Journal of Theoretical Biology"
    1968
    "10.1016/0022-5193(68)90079-9"
    "Motivates parallel developmental rewriting with local cell-state interactions."
    "The finite word grammar is not a complete botanical-development model."

hutchinsonIFSSource : Sources.SourceRecord
hutchinsonIFSSource =
  Sources.sourceRecord
    "John E. Hutchinson"
    "Fractals and self-similarity"
    "Indiana University Mathematics Journal"
    1981
    "10.1512/iumj.1981.30.30055"
    "Motivates recursive contractive systems as a distinct self-similarity generator."
    "Shared fractal statistics do not identify one physical growth process."

yiIntegratedGrowthSource : Sources.SourceRecord
yiIntegratedGrowthSource =
  Sources.sourceRecord
    "Lei Yi; Hongjun Li; Jianwei Guo; Oliver Deussen; Xiaopeng Zhang"
    "Tree Growth Modelling Constrained by Growth Equations"
    "Computer Graphics Forum"
    2018
    "10.1111/cgf.13263"
    "Motivates coupling resource allocation, light sensitivity, space competition, morphology, and growth equations."
    "The finite resource budget is not a calibrated functional-structural plant simulation."

hartSphereTracingSource : Sources.SourceRecord
hartSphereTracingSource =
  Sources.sourceRecord
    "John C. Hart"
    "Sphere tracing: A geometric method for the antialiased ray tracing of implicit surfaces"
    "The Visual Computer"
    1996
    "10.1007/s003710050084"
    "Motivates signed-distance Boolean composition and safe distance-guided ray steps."
    "The finite sign algebra is not an exact Euclidean distance estimator or a literal neural renderer."

canonicalRound3ExtendedSources : List Sources.SourceRecord
canonicalRound3ExtendedSources =
  lindenmayerLSystemSource
  ∷ hutchinsonIFSSource
  ∷ yiIntegratedGrowthSource
  ∷ hartSphereTracingSource
  ∷ []

canonicalRound3ExtendedSourceCount : Nat
canonicalRound3ExtendedSourceCount =
  Sources.listCount canonicalRound3ExtendedSources

canonicalRound3ExtendedSourceCountIsFour :
  canonicalRound3ExtendedSourceCount ≡ 4
canonicalRound3ExtendedSourceCountIsFour = refl
