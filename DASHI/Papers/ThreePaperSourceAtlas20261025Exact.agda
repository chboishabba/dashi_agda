-- Imported legacy owner is not declared --safe; this module contains no
-- postulates or holes but does not claim transitive Safe Agda certification.
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
import DASHI.Core.FirstImplementationTimestampExact as Chronology

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

constantinFefferman1993 : Attribution.AttributedSource
constantinFefferman1993 = Attribution.mkDOISource
  "Peter Constantin; Charles Fefferman"
  "Direction of Vorticity and the Problem of Global Regularity for the Navier-Stokes Equations"
  "Indiana University Mathematics Journal 42(3), 775-789 (1993)"
  "1993"
  "10.1512/iumj.1993.42.42034"
  "https://doi.org/10.1512/iumj.1993.42.42034"
  Attribution.academicArticleSource
  "Geometric direction-of-vorticity precursor; original theorem distinct from Miller's locally varying plane criterion"
  Attribution.publicAttribution

beiraoBerselli2002 : Attribution.AttributedSource
beiraoBerselli2002 = Attribution.mkDOISource
  "Hugo Beirao da Veiga; Luigi C. Berselli"
  "On the regularizing effect of the vorticity direction in incompressible viscous flows"
  "Differential and Integral Equations 15(3), 345-356 (2002)"
  "2002"
  "10.57262/die/1356060864"
  "https://doi.org/10.57262/die/1356060864"
  Attribution.academicArticleSource
  "Vorticity-direction Sobolev criterion that Miller compares; not Miller's theorem and not a DASHI proof"
  Attribution.publicAttribution

wangGalerkin2026 : Attribution.AttributedSource
wangGalerkin2026 = Attribution.mkNoDOISource
  "Weinan Wang"
  "Formalization of the Galerkin Construction for the Two-Dimensional Navier-Stokes Equations in Lean"
  "arXiv:2609.33033, submitted 2026-09-27"
  "2026"
  "https://arxiv.org/abs/2609.33033"
  Attribution.academicArticleSource
  "Independent 2D Lean formalisation reference; source of potential general Hilbert-space transport tools, NOT a solution to 3D A3 or proof imported into this repository"
  Attribution.publicAttribution

semanticFidelityCritique2026 : Attribution.AttributedSource
semanticFidelityCritique2026 = Attribution.mkNoDOISource
  "Alexander Bastounis; Fabian Circelli; Anders C. Hansen"
  "Navier-Stokes lost in translation: Why Lean verification of AI autoformalisation does not guarantee correct natural language proofs"
  "arXiv:2610.08144, first posted 2026-10-06; methodological critique, not independently adjudicated as a theorem by DASHI"
  "2026"
  "https://arxiv.org/abs/2610.08144"
  Attribution.academicArticleSource
  "Author-claimed semantic noncorrespondence and autoformalisation limits in the 2026 OpenAI Navier-Stokes example; does not challenge soundness of the Lean kernel. DASHI proves distinct finite source-hypothesis erasure no-gos; does not adopt allegations as mathematical facts."
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
    ∷ constantinFefferman1993
    ∷ beiraoBerselli2002
    ∷ wangGalerkin2026
    ∷ semanticFidelityCritique2026
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


------------------------------------------------------------------------
-- FIRST SOURCE-COMMIT RECEIPTS. These are author+date source provenance,
-- NOT kernel/typecheck/publication dates. Existing generic owner reused.
--
-- UTC commit timestamps were recovered from GitHub commit objects, not
-- inferred from PR creation or later review. Australia/Brisbane is UTC+10.
-- Original external authors retain their much earlier publication priority.
-- Formal construction here: Johl Brown-directed DASHI research, with
-- OpenAI ChatGPT-assisted implementations on the attributed commit objects.
------------------------------------------------------------------------

rodgersFiniteOwnerFirstImplementation :
  Chronology.FirstImplementationReceipt
rodgersFiniteOwnerFirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Cognition.PNF.EnactedTemporalOrderExact"
    "85a4e6121914396e9d106b0d3c0535892f1034ae"
    "2026-10-24T18:00:21Z"
    "2026-10-25T04:00:21+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly

millerA3FirstImplementation :
  Chronology.FirstImplementationReceipt
millerA3FirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Physics.Closure.NSMillerAnisotropicA3BridgeExact"
    "c77c27569603a8ca35eb76e8b61c79575221d2f2"
    "2026-10-24T18:01:18Z"
    "2026-10-25T04:01:18+10:00"
    "Australia/Brisbane"
    Chronology.openConsumerImplemented
    Chronology.sourceCommittedOnly

yanPressureFirstImplementation :
  Chronology.FirstImplementationReceipt
yanPressureFirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Physics.Closure.NSYanRadulescuStationaryPressureExact"
    "32c74ca3df59bdacc9909a4555d6033ea5b622e5"
    "2026-10-24T18:01:38Z"
    "2026-10-25T04:01:38+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly

yanLeanCubeFirstImplementation :
  Chronology.FirstImplementationReceipt
yanLeanCubeFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.YanRadulescuCubeSeed"
    "176679d666f8c8c2c20ad82c4c91d9fc9e5f4f02"
    "2026-10-25T08:16:07Z"
    "2026-10-25T18:16:07+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly


-- The following are new, distinct implementation objects on 26 October.
-- Refactor dates are not substituted for these first-source-commit receipts.
yanExactLeanSeedFirstImplementation :
  Chronology.FirstImplementationReceipt
yanExactLeanSeedFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.YanRadulescuExactSeed"
    "15f19895bf7432c8de631ecf6224738127f28c86"
    "2026-10-26T11:17:39Z"
    "2026-10-26T21:17:39+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly

yanAdversePressureFirstImplementation :
  Chronology.FirstImplementationReceipt
yanAdversePressureFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.YanRadulescuPressureCountermodel"
    "0f55d6666943fe016ee15abda1eaea0d8d52822d"
    "2026-10-26T11:20:23Z"
    "2026-10-26T21:20:23+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly

rodgersArrivalCollisionFirstImplementation :
  Chronology.FirstImplementationReceipt
rodgersArrivalCollisionFirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Cognition.PNF.EnactedTemporalOrderExact / labelled arrival collision"
    "0a2787dfd657e35a672046a3370c0ceacff75f2b"
    "2026-10-26T11:26:32Z"
    "2026-10-26T21:26:32+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly


-- First implementation: source-written finite vector projection, not a
-- completed L4_t L2_x same-solution NS bound or Lean kernel receipt.
millerProjectionFirstImplementation :
  Chronology.FirstImplementationReceipt
millerProjectionFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.MillerProjectionGeometry"
    "ea36d97a74f9be9b2d71b6015b926216ffc01ec4"
    "2026-10-26T12:14:54Z"
    "2026-10-26T22:14:54+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly

-- First implementation: source-hypothesis-erasure witnesses, not an
-- external finding or a complete proof correspondence checker.
semanticFidelityWitnessFirstImplementation :
  Chronology.FirstImplementationReceipt
semanticFidelityWitnessFirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Papers.ThreePaperConsumerFidelity20261026Exact"
    "0b8ae8b07ee575c6ed964d3dd634292d45a0a973"
    "2026-10-26T12:17:53Z"
    "2026-10-26T22:17:53+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly


-- Separate new declaration in a pre-existing source file. First appearance
-- of this lemma is not the first appearance of the containing file.
millerFiniteSampleBudgetFirstImplementation :
  Chronology.FirstImplementationReceipt
millerFiniteSampleBudgetFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.MillerProjectionGeometry.finite_sample_fourth_power_budget"
    "10681b456753e354e10d77eec065270d7a1c3612"
    "2026-10-26T12:19:22Z"
    "2026-10-26T22:19:22+10:00"
    "Australia/Brisbane"
    Chronology.completedProofImplemented
    Chronology.sourceCommittedOnly

-- This is a separately executed finite symbolic source consistency check,
-- not the full vector PDE formalization nor a kernel-exact theorem.
yanThreeDimensionalSymbolicAuditFirstImplementation :
  Chronology.FirstImplementationReceipt
yanThreeDimensionalSymbolicAuditFirstImplementation =
  Chronology.first-implementation-receipt
    "scripts/check_ns_pressure_divergence_exact.py"
    "620e35069f050018918ca8d6e38933cad5cda840"
    "2026-10-26T12:25:30Z"
    "2026-10-26T22:25:30+10:00"
    "Australia/Brisbane"
    Chronology.candidateReceiptImplemented
    Chronology.sourceCommittedOnly


-- The finite two-point steep-direction theorem extends a pre-existing
-- Lean projection module. This SHA is the lemma's first implementation,
-- not the module's initial SHA, and is NOT a Lean kernel verification.
millerSteepDirectionFirstImplementation :
  Chronology.FirstImplementationReceipt
millerSteepDirectionFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.MillerProjectionGeometry.finite_zero_projection_allows_arbitrarily_steep_slope"
    "631b9833e5e5b1cff20ab975cf4ae4354d246fe2"
    "2026-10-26T14:27:10Z"
    "2026-10-27T00:27:10+10:00"
    "Australia/Brisbane"
    Chronology.completedProofImplemented
    Chronology.sourceCommittedOnly

-- Weighted quadrature is a finite Lemma, not L4_t L2_x convergence.
millerWeightedQuadratureFirstImplementation :
  Chronology.FirstImplementationReceipt
millerWeightedQuadratureFirstImplementation =
  Chronology.first-implementation-receipt
    "RequestProject.NavierStokes.MillerProjectionGeometry.weighted_sample_fourth_power_budget"
    "5445472af7c3af8e141e10859b92c653f3a43162"
    "2026-10-26T14:30:44Z"
    "2026-10-27T00:30:44+10:00"
    "Australia/Brisbane"
    Chronology.completedProofImplemented
    Chronology.sourceCommittedOnly

-- The source-blind direction-gradient collision explicitly REUSES the
-- original generic DASHI core rather than changing its ownership.
millerDirectionFidelityFirstImplementation :
  Chronology.FirstImplementationReceipt
millerDirectionFidelityFirstImplementation =
  Chronology.first-implementation-receipt
    "DASHI.Papers.ThreePaperConsumerFidelity20261026Exact.projectedVorticityGradientLossWitness"
    "72c2419069b95d25a6e7f076e0bb3d82b8c82d0a"
    "2026-10-26T14:32:09Z"
    "2026-10-27T00:32:09+10:00"
    "Australia/Brisbane"
    Chronology.exactRepresentationImplemented
    Chronology.sourceCommittedOnly
