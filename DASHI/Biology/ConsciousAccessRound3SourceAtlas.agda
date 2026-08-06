module DASHI.Biology.ConsciousAccessRound3SourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attributed source atlas for visual phenomenology, morphogenesis,
-- recursive packing, and retinotopic geometry.

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    importedRole : String
    excludedPromotion : String

open SourceRecord public

turingMorphogenesisSource : SourceRecord
turingMorphogenesisSource =
  sourceRecord
    "Alan M. Turing"
    "The Chemical Basis of Morphogenesis"
    "Philosophical Transactions of the Royal Society B"
    1952
    "10.1098/rstb.1952.0012"
    "Motivates finite local-excitation and lateral-inhibition mode selection."
    "The finite mode witness is not a calibrated tissue or cortical reaction-diffusion model."

smithPhyllotaxisSource : SourceRecord
smithPhyllotaxisSource =
  sourceRecord
    "Richard S. Smith; Soazig Guyomarc'h; Therese Mandel; Didier Reinhardt; Cris Kuhlemeier; Przemyslaw Prusinkiewicz"
    "A plausible model of phyllotaxis"
    "Proceedings of the National Academy of Sciences"
    2006
    "10.1073/pnas.0510457103"
    "Motivates sequential site selection by transported signal and inhibition from existing primordia."
    "The cortical model is not claimed to use literal auxin or PIN-mediated transport."

runionsSpaceColonizationSource : SourceRecord
runionsSpaceColonizationSource =
  sourceRecord
    "Adam Runions; Brendan Lane; Przemyslaw Prusinkiewicz"
    "Modeling Trees with a Space Colonization Algorithm"
    "Eurographics Workshop on Natural Phenomena"
    2007
    "10.2312/NPH/NPH07/063-070"
    "Motivates environment-constrained growth toward residual attraction sites."
    "A negative-space cavity model is not identified with botanical tree growth."

wittenSanderDLASource : SourceRecord
wittenSanderDLASource =
  sourceRecord
    "T. A. Witten Jr.; L. M. Sander"
    "Diffusion-Limited Aggregation, a Kinetic Critical Phenomenon"
    "Physical Review Letters"
    1981
    "10.1103/PhysRevLett.47.1400"
    "Motivates a distinct stochastic accretive universality class for dendritic geometry."
    "Smooth sphere-perforated passages are not inferred to be DLA-generated."

borkovecApollonianSource : SourceRecord
borkovecApollonianSource =
  sourceRecord
    "M. Borkovec; W. de Paris; R. Peikert"
    "The Fractal Dimension of the Apollonian Sphere Packing"
    "Fractals"
    1994
    "10.1142/S0218348X94000739"
    "Motivates tangency-driven multiscale packing and the distinction between periodic and local-rule regularity."
    "The remembered hall is not asserted to be a unique inverse Apollonian construction."

schwartzLogPolarSource : SourceRecord
schwartzLogPolarSource =
  sourceRecord
    "Eric L. Schwartz"
    "Computational anatomy and functional architecture of striate cortex: a spatial mapping approach to perceptual coding"
    "Vision Research"
    1980
    "10.1016/0042-6989(80)90090-5"
    "Motivates the finite complex-log analogy turning scale and rotation into cortical translation."
    "The retina or V1 is not treated as an exact ideal log-polar grid."

taQuasiconformalSource : SourceRecord
taQuasiconformalSource =
  sourceRecord
    "Duyan Ta; Yanshuai Tu; Zhong-Lin Lu; Yalin Wang"
    "Quantitative Characterization of the Human Retinotopic Map Based on Quasiconformal Mapping"
    "Medical Image Analysis"
    2022
    "10.1016/j.media.2021.102230"
    "Motivates treating measured human retinotopy as structured but non-ideal and quasiconformal."
    "The finite coordinate map is not promoted to a fitted human retinotopic atlas."

shenVisualReportsSource : SourceRecord
shenVisualReportsSource =
  sourceRecord
    "Sean Noah Miranda Shen; Earth Erowid; Fire Erowid; Michael Silver"
    "A novel method for quantitative analysis of subjective experience reports: application to psychedelic visual experiences"
    "Frontiers in Psychology"
    2024
    "10.3389/fpsyg.2024.1397064"
    "Motivates substance-indexed and feature-indexed visual-effect profiles rather than one scalar visual intensity."
    "Text-report differences are not sufficient to identify receptor-level mechanisms."

simonssonLongitudinalVisualSource : SourceRecord
simonssonLongitudinalVisualSource =
  sourceRecord
    "Otto Simonsson; Peter S. Hendricks; Cecilia U. D. Stenfors; Simon B. Goldberg; Ludwig Honk; Walter Osika"
    "Longitudinal associations between psychedelic use and unusual visual experiences in the United States and the United Kingdom"
    "Journal of Psychopharmacology"
    2024
    "10.1177/02698811231218931"
    "Motivates a separate slow adaptation state for post-acute unusual visual experience."
    "Association is not promoted to universal causation, HPPD diagnosis, or a single persistent mechanism."

canonicalRound3Sources : List SourceRecord
canonicalRound3Sources =
  turingMorphogenesisSource
  ∷ smithPhyllotaxisSource
  ∷ runionsSpaceColonizationSource
  ∷ wittenSanderDLASource
  ∷ borkovecApollonianSource
  ∷ schwartzLogPolarSource
  ∷ taQuasiconformalSource
  ∷ shenVisualReportsSource
  ∷ simonssonLongitudinalVisualSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalRound3SourceCount : Nat
canonicalRound3SourceCount = listCount canonicalRound3Sources

canonicalRound3SourceCountIsNine :
  canonicalRound3SourceCount ≡ 9
canonicalRound3SourceCountIsNine = refl
