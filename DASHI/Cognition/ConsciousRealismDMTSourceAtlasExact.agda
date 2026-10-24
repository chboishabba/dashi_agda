module DASHI.Cognition.ConsciousRealismDMTSourceAtlasExact where

-- Source attribution is non-promoting. Original source authors retain credit;
-- DASHI owns only the local formalisation, finite audit, and model comparison.
-- The trace-chain preprint was posted in 2024; TRACE labels its 2025 result.
open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

hoffmanPrakash2014 : Source.AttributedSource
hoffmanPrakash2014 = Source.mkDOISource
  "Donald D. Hoffman; Chetan Prakash"
  "Objects of Consciousness"
  "Frontiers in Psychology 5:577; published 17 June 2014"
  "2014"
  "10.3389/fpsyg.2014.00577"
  "https://doi.org/10.3389/fpsyg.2014.00577"
  Source.academicArticleSource
  "conscious-agent stochastic perception/decision/action kernels; not DASHI identifiability"
  Source.publicAttribution

hoffmanPrakashPrentner2023 : Source.AttributedSource
hoffmanPrakashPrentner2023 = Source.mkDOISource
  "Donald D. Hoffman; Chetan Prakash; Robert Prentner"
  "Fusions of Consciousness"
  "Entropy 25(1):129"
  "2023"
  "10.3390/e25010129"
  "https://doi.org/10.3390/e25010129"
  Source.academicArticleSource
  "source of Q=DAP and agent combination/fusion; not evidence of DMT entities"
  Source.publicAttribution

hoffmanPrakashChattopadhyayTrace : Source.AttributedSource
hoffmanPrakashChattopadhyayTrace = Source.mkNoDOISource
  "Donald D. Hoffman; Chetan Prakash; Swapan Chattopadhyay"
  "Traces of Consciousness"
  "Preprints.org v1 posted 17 October 2024; TRACE describes 2025 trace-chain result"
  "2024"
  "https://www.preprints.org/manuscript/202410.1305"
  Source.academicArticleSource
  "source of trace-chain formula/order; DASHI finite toy audit is independently derived"
  Source.publicAttribution

gallimoreHermanssonHoffman2026 : Source.AttributedSource
gallimoreHermanssonHoffman2026 = Source.mkDOISource
  "Andrew Robert Gallimore; Niffe Hermansson; Donald D. Hoffman"
  "Traces of the Other: Are DMT Entities Real? DMT Phenomenology in the Framework of Conscious Realism"
  "PsyArXiv preprint v2, 27 May 2026"
  "2026"
  "10.31234/osf.io/8qvgy_v2"
  "https://doi.org/10.31234/osf.io/8qvgy_v2"
  Source.academicArticleSource
  "DMT interface/other-agent conjecture and proposed experiments; no confirmed entities"
  Source.publicAttribution

janCordon2026 : Source.AttributedSource
janCordon2026 = Source.mkDOISource
  "Damián Enrique Jan-Cordón"
  "The Trace Term as the Empirical Target: A Commentary on Traces of the Other"
  "SSRN commentary written 18 July, posted 3 August 2026"
  "2026"
  "10.2139/ssrn.7139998"
  "https://doi.org/10.2139/ssrn.7139998"
  Source.academicArticleSource
  "independent commentary on cooperation/semantic nuisance nonidentification; not experimental data"
  Source.publicAttribution

consciousRealismDMTSourceAtlas : Source.AttributedSourceAtlas
consciousRealismDMTSourceAtlas = Source.mkSourceAtlas
  "conscious realism / DMT claim-bounded source atlas"
  "DASHI.Cognition.ConsciousRealismDMTSourceAtlasExact"
  (hoffmanPrakash2014 ∷ hoffmanPrakashPrentner2023 ∷
   hoffmanPrakashChattopadhyayTrace ∷ gallimoreHermanssonHoffman2026 ∷
   janCordon2026 ∷ [])
  "five original-author lineages; separate proof vs conjecture vs critique; citation imports nothing"

atlasNonPromoting :
  Source.AttributedSourceAtlas.atlasCreatesAuthority
    consciousRealismDMTSourceAtlas ≡ false
atlasNonPromoting = refl
