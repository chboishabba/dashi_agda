module DASHI.Foundations.AutoformalisationBCH2026Sources where

-- Original authorship and fixed historical evidence objects.
-- Citations, code-permalinks and arguments each have different authority.
-- No secondary review, mirror or source code counts as a separate
-- independent corroboration of BCH2026 or the OpenAI PDE results.

open import Agda.Builtin.List using ([]; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.FirstImplementationTimestampExact as Chronology

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

cameronFreerHilbert10 : Source.AttributedSource
cameronFreerHilbert10 = Source.mkNoDOISource
  "Cameron Freer"
  "Hilbert's tenth problem in Lean"
  "Original Apache-2.0 Lean 4 software, CITATION.cff v2.4.0 (2026); public Hilbert10 DPRM and H10 endpoints"
  "2026"
  "https://github.com/cameronfreer/hilbert10"
  (Source.namedSourceKind "independent open-source Lean formalisation software")
  "Repository reports proved semantic DPRM dioph_iff_rePred, RE-complete NatSolvable and an existential universal polynomial with unspecified witness count k. This is a DONOR; does not itself claim k<=9, Sigma_l completeness or BCH2026 SCI infinity. Different Lean/mathlib pins mean no direct import was executed."
  Source.publicAttribution

originalSourceAtlas : Source.AttributedSourceAtlas
originalSourceAtlas = Source.mkSourceAtlas
  "BCH2026 autoformalisation audit with NL manuscript and fixed Lean history"
  "DASHI.Foundations.AutoformalisationBCH2026Sources"
  (bchOriginal2026 ∷ openaiHistoricalCode2026 ∷ openaiNaturalProof2026 ∷ cameronFreerHilbert10 ∷ [])
  "One original BCH2026 paper root (arXiv and mirrors are not independent); separate OpenAI paper/code evidence objects. Author-claimed discrepancies, formalised finite reconstructions, and kernel receipts have distinct provenance."

bchSnowball : Snowball.SourceRoleSnowballReceipt bchOriginal2026
bchSnowball = Snowball.canonicalSourceRoleSnowballReceipt bchOriginal2026

historicalCodeSnowball :
  Snowball.SourceRoleSnowballReceipt openaiHistoricalCode2026
historicalCodeSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt openaiHistoricalCode2026


-- Original BCH article precedence is 2026-10-06. These code receipts
-- record GitHub's first source commits for the DASHI reconstruction.
-- They are NOT first paper priority, not Lean/Agda kernel success,
-- and not evidence of source-to-NL equivalence.

leanExamplesFirstSourceCommit : Chronology.FirstImplementationReceipt
leanExamplesFirstSourceCommit =
  Chronology.first-implementation-receipt
    "RequestProject.Autoformalisation.LostInTranslationExamples"
    "ced014584754c53883f7650fda2c00ce6cb06f65"
    "2026-10-26T15:01:57Z"
    "2026-10-27T01:01:57+10:00"
    "Australia/Brisbane"
    Chronology.theoremStatementImplemented
    Chronology.sourceCommittedOnly

leanSCIInterfaceFirstSourceCommit : Chronology.FirstImplementationReceipt
leanSCIInterfaceFirstSourceCommit =
  Chronology.first-implementation-receipt
    "RequestProject.Autoformalisation.LostInTranslationSCI"
    "00f57929ab3790ecad02496ccfe87d44b823cfb2"
    "2026-10-26T15:03:06Z"
    "2026-10-27T01:03:06+10:00"
    "Australia/Brisbane"
    Chronology.openConsumerImplemented
    Chronology.sourceCommittedOnly

agdaFiniteOwnersFirstSourceCommit : Chronology.FirstImplementationReceipt
agdaFiniteOwnersFirstSourceCommit =
  Chronology.first-implementation-receipt
    "DASHI.Foundations.AutoformalisationBCH2026Exact"
    "4a278506c7805a73e34cae1029a283d1f01f1b91"
    "2026-10-26T15:05:55Z"
    "2026-10-27T01:05:55+10:00"
    "Australia/Brisbane"
    Chronology.theoremStatementImplemented
    Chronology.sourceCommittedOnly

freerDonorSnowball :
  Snowball.SourceRoleSnowballReceipt cameronFreerHilbert10
freerDonorSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt cameronFreerHilbert10
