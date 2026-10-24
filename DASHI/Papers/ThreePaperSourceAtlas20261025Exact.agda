{-# OPTIONS --safe #-}
module DASHI.Papers.ThreePaperSourceAtlas20261025Exact where

-- Attribution owner for three user-supplied primary paper objects.
-- Identifiers are reported from their source documents. Rodgers's
-- 2026-10-23 Zenodo DOI appears in the supplied PDF; an independent
-- resolver/identity check is not implied by putting it in this atlas.
-- Related work is genealogy, not independent replication or source
-- ownership of the DASHI constructions.
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Core.AttributedSourceCore as Attribution using ()
open import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball using ()

miller2021 : Attribution.AttributedSource
miller2021 = Attribution.mkDOISource
  "Evan Miller"
  "A Locally Anisotropic Regularity Criterion for the Navier-Stokes Equation in Terms of Vorticity"
  "Proceedings of the American Mathematical Society, Series B 8, 60-74 (2021)"
  "2021"
  "10.1090/bproc/74"
  "https://doi.org/10.1090/bproc/74"
  Attribution.academicArticleSource
  "Published Theorem 1.6 / proof in Section 2; DASHI models an algebraic and conditional continuation bridge, not an unconditional regularity theorem"
  Attribution.publicAttribution

yanRadulescu2021 : Attribution.AttributedSource
yanRadulescu2021 = Attribution.mkDOISource
  "Weiping Yan; Vicentiu D. Radulescu"
  "Sobolev regular solutions for the incompressible Navier-Stokes equations in higher dimensions: asymptotics and representation formulae"
  "Rendiconti del Circolo Matematico di Palermo, Series 2, 70, 995-1021 (2021); online 2020-07-25"
  "2021"
  "10.1007/s12215-020-00540-3"
  "https://doi.org/10.1007/s12215-020-00540-3"
  Attribution.academicArticleSource
  "Source Theorem 1.1 and Corollary 1.1 on STEADY forced bounded-domain solutions; pressure forcing-divergence audit is independently derived and not attributed as their theorem"
  Attribution.publicAttribution

rodgers2026 : Attribution.AttributedSource
rodgers2026 = Attribution.mkDOISource
  "Jeremy Rodgers"
  "Experienced Temporal Passage: Enacted Scaffolding and the Organization of Succession"
  "Independent researcher manuscript, dated 2026-10-23; Zenodo DOI printed in supplied PDF"
  "2026"
  "10.5281/zenodo.23591626"
  "https://doi.org/10.5281/zenodo.23591626"
  Attribution.academicArticleSource
  "Proposition 1 and Appendix C motivate finite order and admission checks; constitutive premises and experienced character are not established by finite model proofs"
  Attribution.publicAttribution

chaeChoe1999 : Attribution.AttributedSource
chaeChoe1999 = Attribution.mkNoDOISource
  "Dongho Chae; Hi-Jun Choe"
  "Regularity of solutions to the Navier-Stokes equation"
  "Electronic Journal of Differential Equations 1999, No. 05, pp. 1-7"
  "1999"
  "https://ejde.math.txstate.edu/Volumes/1999/05/abstr.html"
  Attribution.academicArticleSource
  "Historical two-component vorticity regularity predecessor cited by Miller; not independently re-proved here"
  Attribution.publicAttribution

openaiForced2026 : Attribution.AttributedSource
openaiForced2026 = Attribution.mkNoDOISource
  "OpenAI"
  "Finite time blowup for Navier-Stokes"
  "OpenAI research release and associated Lean repository, 2026-09-08"
  "2026"
  "https://github.com/openai/NavierStokesAndEuler"
  Attribution.academicArticleSource
  "Separate smooth-FORCED Clay C/D breakdown result; NOT an unforced A/B theorem, not the proof of Miller's continuation hypothesis, not a result claimed by DASHI"
  Attribution.publicAttribution

threePaperAtlas : Attribution.AttributedSourceAtlas
threePaperAtlas = Attribution.mkSourceAtlas
  "Miller / Yan-Radulescu / Rodgers primary-paper and source-genealogy cut"
  "DASHI.Papers.ThreePaperSourceAtlas20261025Exact"
  (miller2021
    ∷ yanRadulescu2021
    ∷ rodgers2026
    ∷ chaeChoe1999
    ∷ openaiForced2026
    ∷ [])
  "Each row is a source role with distinct assumptions and original authorship. Reprints, bibliography edges and typed reconstruction are not independent corroboration, kernel proofs, or physical admission."

millerSnowball : Snowball.SourceRoleSnowballReceipt miller2021
millerSnowball = Snowball.canonicalSourceRoleSnowballReceipt miller2021

yanSnowball : Snowball.SourceRoleSnowballReceipt yanRadulescu2021
yanSnowball = Snowball.canonicalSourceRoleSnowballReceipt yanRadulescu2021

rodgersSnowball : Snowball.SourceRoleSnowballReceipt rodgers2026
rodgersSnowball = Snowball.canonicalSourceRoleSnowballReceipt rodgers2026

openaiForcedSnowball : Snowball.SourceRoleSnowballReceipt openaiForced2026
openaiForcedSnowball = Snowball.canonicalSourceRoleSnowballReceipt openaiForced2026
