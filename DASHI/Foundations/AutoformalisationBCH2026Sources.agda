module DASHI.Foundations.AutoformalisationBCH2026Sources where

-- Original authorship and fixed historical evidence objects.
-- Citations, code-permalinks and arguments each have different authority.
-- No secondary review, mirror or source code counts as a separate
-- independent corroboration of BCH2026 or the OpenAI PDE results.

open import Agda.Builtin.List using ([]; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

bchOriginal2026 : Source.AttributedSource
bchOriginal2026 = Source.mkDOISource
  "Alexander Bastounis; Fabian Circelli; Anders C. Hansen"
  "Navier-Stokes lost in translation: Why Lean verification of AI autoformalisation does not guarantee correct natural language proofs"
  "arXiv:2610.08144v1, first posted 2026-10-06, 25 pages, 4 figures"
  "2026"
  "10.48550/arXiv.2610.08144"
  "https://arxiv.org/html/2610.08144v1"
  Source.academicArticleSource
  "Original authors' argument and Appendix A completeness claims. This project reconstructs finite witnesses and leaves DPRM/SCI completeness outstanding; article existence is not independent proof of its full claims."
  Source.publicAttribution

openaiHistoricalCode2026 : Source.AttributedSource
openaiHistoricalCode2026 = Source.mkNoDOISource
  "OpenAI"
  "NavierStokesAndEuler: historical Lean source at f9e8bc5"
  "GitHub commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd, audited by BCH2026; not current HEAD"
  "2026"
  "https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
  Source.institutionalSource
  "Original exact machine-checked theorem source; code existence is distinct from natural-language manuscript equivalence, and the critique's historical commit is not assumed to match later revisions."
  Source.publicAttribution

openaiNaturalProof2026 : Source.AttributedSource
openaiNaturalProof2026 = Source.mkNoDOISource
  "OpenAI"
  "Finite time blowup for Navier-Stokes"
  "Original 2026 smooth-forced blowup manuscript; compare Lemma 8.6 (8.19) and Lemma 10.5 (10.19)"
  "2026"
  "https://openai.com/index/navier-stokes-solution/"
  Source.institutionalSource
  "Distinct NL manuscript object; a proof of a related Lean theorem does not certify every theorem statement or proof route in this PDF."
  Source.publicAttribution

originalSourceAtlas : Source.AttributedSourceAtlas
originalSourceAtlas = Source.mkSourceAtlas
  "BCH2026 autoformalisation audit with NL manuscript and fixed Lean history"
  "DASHI.Foundations.AutoformalisationBCH2026Sources"
  (bchOriginal2026 ∷ openaiHistoricalCode2026 ∷ openaiNaturalProof2026 ∷ [])
  "One original BCH2026 paper root (arXiv and mirrors are not independent); separate OpenAI paper/code evidence objects. Author-claimed discrepancies, formalised finite reconstructions, and kernel receipts have distinct provenance."

bchSnowball : Snowball.SourceRoleSnowballReceipt bchOriginal2026
bchSnowball = Snowball.canonicalSourceRoleSnowballReceipt bchOriginal2026

historicalCodeSnowball :
  Snowball.SourceRoleSnowballReceipt openaiHistoricalCode2026
historicalCodeSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt openaiHistoricalCode2026
