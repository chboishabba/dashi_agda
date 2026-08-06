module DASHI.Physics.DarkSector.DarkSectorColliderSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Primary and review sources for the collider-facing hidden-sector tranche.
-- The records support operator, lifetime, geometry, and trigger semantics but
-- do not promote the finite Agda witnesses to calibrated phenomenology.

silveiraZeeSource : Sources.SourceRecord
silveiraZeeSource =
  Sources.sourceRecord
    "Vanda Silveira; A. Zee"
    "Scalar Phantoms"
    "Physics Letters B"
    1985
    "10.1016/0370-2693(85)90624-0"
    "Supports a gauge-singlet scalar coupled through the Higgs-sector invariant."
    "The canonical finite portal operator is not a quantitative scalar-phantom model."

schabingerWellsSource : Sources.SourceRecord
schabingerWellsSource =
  Sources.sourceRecord
    "Robert M. Schabinger; James D. Wells"
    "A Minimal Spontaneously Broken Hidden Sector and its Impact on Higgs Boson Physics at the Large Hadron Collider"
    "Physical Review D"
    2005
    "10.1103/PhysRevD.72.093007"
    "Supports Higgs mixing and visible collider consequences of a minimal hidden scalar sector."
    "The finite decay graph does not calculate mixing angles, widths, or LHC cross sections."

pattWilczekSource : Sources.SourceRecord
pattWilczekSource =
  Sources.sourceRecord
    "Brian Patt; Frank Wilczek"
    "Higgs-field Portal into Hidden Sectors"
    "arXiv high energy phenomenology"
    2006
    "10.48550/arXiv.hep-ph/0605188"
    "Supports the gauge-invariant Higgs portal as an interaction between visible and hidden singlet operators."
    "Portal admissibility alone does not establish a realised dark sector or branching fraction."

alimenaLLPReviewSource : Sources.SourceRecord
alimenaLLPReviewSource =
  Sources.sourceRecord
    "Juliette Alimena et al."
    "Searching for Long-Lived Particles beyond the Standard Model at the Large Hadron Collider"
    "Journal of Physics G: Nuclear and Particle Physics"
    2020
    "10.1088/1361-6471/ab4574"
    "Supports the lifetime, boosted displacement, detector-acceptance, and trigger taxonomy of collider long-lived particles."
    "The finite tick and Nat-distance model is not a detector simulation or continuum decay distribution."

cmsDisplacedDimuonSource : Sources.SourceRecord
cmsDisplacedDimuonSource =
  Sources.sourceRecord
    "CMS Collaboration"
    "Search for Long-Lived Particles Decaying to Final States with a Pair of Muons in Proton-Proton Collisions at sqrt(s) = 13.6 TeV"
    "Journal of High Energy Physics"
    2024
    "10.1007/JHEP05(2024)047"
    "Supports displaced-dimuon reconstruction, dedicated trigger acceptance, and Higgs-to-long-lived-particle interpretations."
    "The canonical displaced event is not evidence for a CMS signal or an exclusion limit."

cmsLLPTriggerSource : Sources.SourceRecord
cmsLLPTriggerSource =
  Sources.sourceRecord
    "CMS Collaboration"
    "Strategy and Performance of the CMS Long-Lived Particle Trigger Program in Proton-Proton Collisions at sqrt(s) = 13.6 TeV"
    "CMS-EXO-23-016; submitted to Physics Reports"
    2026
    "10.48550/arXiv.2601.17544"
    "Supports treating prompt and displaced online selections as distinct lossy observation channels."
    "The finite prompt-versus-LLP trigger table is not a model of the complete CMS trigger menu or performance."

canonicalDarkSectorColliderSources : List Sources.SourceRecord
canonicalDarkSectorColliderSources =
  silveiraZeeSource
  ∷ schabingerWellsSource
  ∷ pattWilczekSource
  ∷ alimenaLLPReviewSource
  ∷ cmsDisplacedDimuonSource
  ∷ cmsLLPTriggerSource
  ∷ []

darkSectorSourceCount : List Sources.SourceRecord → Nat
darkSectorSourceCount [] = 0
darkSectorSourceCount (_ ∷ sources) = suc (darkSectorSourceCount sources)

canonicalDarkSectorColliderSourceCount : Nat
canonicalDarkSectorColliderSourceCount =
  darkSectorSourceCount canonicalDarkSectorColliderSources

canonicalDarkSectorColliderSourceCountIsSix :
  canonicalDarkSectorColliderSourceCount ≡ 6
canonicalDarkSectorColliderSourceCountIsSix = refl
