module DASHI.Analysis.CollatzSyracuseSOTA2026Exact where

------------------------------------------------------------------------
-- ATTRIBUTION-SAFE COLLATZ / SYRACUSE SOTA ATLAS
--
-- This owner records external source identity and the bounded role for which
-- each source is relevant to the current DASHI Collatz max-cut.  It does NOT
-- import an external theorem into Agda and does NOT promote almost-all,
-- finite-verification, cycle-exclusion, coefficient-stopping, automaton, or
-- parity-vector results to the universal Collatz conjecture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Claim-relative source roles.
------------------------------------------------------------------------

data CollatzSourceRole : Set where
  almostAllSyracuseTransportRole : CollatzSourceRole
  paradoxicalFiniteSequenceRole : CollatzSourceRole
  parityVectorDensityPreprintRole : CollatzSourceRole
  finiteVerificationRole : CollatzSourceRole
  verificationAlgorithmPreprintRole : CollatzSourceRole
  maximalTypicalHorizonPreprintRole : CollatzSourceRole
  nontrivialCycleExclusionRole : CollatzSourceRole
  foundationalCoefficientStoppingRole : CollatzSourceRole
  coefficientStoppingSurveyRole : CollatzSourceRole
  binaryTernaryAutomatonRole : CollatzSourceRole
  coefficientStoppingTreePreprintRole : CollatzSourceRole
  semiconvergentPassagePreprintRole : CollatzSourceRole

data PublicationStatus : Set where
  peerReviewed : PublicationStatus
  preprint : PublicationStatus
  peerReviewedWithCorrigendum : PublicationStatus

record CollatzSourceAdmission : Set where
  constructor collatzSourceAdmission
  field
    source : Source.AttributedSource
    role : CollatzSourceRole
    status : PublicationStatus

open CollatzSourceAdmission public

------------------------------------------------------------------------
-- Peer-reviewed sources.
------------------------------------------------------------------------

tao2022 : Source.AttributedSource
tao2022 =
  Source.mkDOISource
    "Terence Tao"
    "Almost all orbits of the Collatz map attain almost bounded values"
    "Forum of Mathematics, Pi 10, e12"
    "2022"
    "10.1017/fmp.2022.8"
    "https://doi.org/10.1017/fmp.2022.8"
    Source.academicArticleSource
    "published almost-all logarithmic-density theorem using the Syracuse iteration, first-passage transport, 3-adic cyclic groups, and Fourier decay; source role only"
    Source.publicAttribution

rozierTerracol2026 : Source.AttributedSource
rozierTerracol2026 =
  Source.mkDOISource
    "Olivier Rozier; Claude Terracol"
    "Paradoxical behavior in Collatz sequences"
    "Discrete Mathematics 349(10), 115167"
    "2026"
    "10.1016/j.disc.2026.115167"
    "https://doi.org/10.1016/j.disc.2026.115167"
    Source.academicArticleSource
    "published finite-sequence paradoxical-behavior analysis; motivates keeping parity proportion separate from the affine correction and is not imported as a universal Collatz theorem"
    Source.publicAttribution

barina2025 : Source.AttributedSource
barina2025 =
  Source.mkDOISource
    "David Barina"
    "Improved verification limit for the convergence of the Collatz conjecture"
    "The Journal of Supercomputing 81, 810"
    "2025"
    "10.1007/s11227-025-07337-0"
    "https://doi.org/10.1007/s11227-025-07337-0"
    Source.academicArticleSource
    "peer-reviewed computational verification through 2^71; finite verification evidence only"
    Source.publicAttribution

hercher2023 : Source.AttributedSource
hercher2023 =
  Source.mkNoDOISource
    "Christian Hercher"
    "There are no Collatz m-Cycles with m <= 91"
    "Journal of Integer Sequences 26, Article 23.3.5; corrigendum June 2026"
    "2023"
    "https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html"
    Source.academicArticleSource
    "peer-reviewed nontrivial-cycle exclusion with a 2026 corrigendum; cycle exclusion remains distinct from exclusion of divergent nonperiodic trajectories"
    Source.publicAttribution

terras1976 : Source.AttributedSource
terras1976 =
  Source.mkDOISource
    "Riho Terras"
    "A stopping time problem on the positive integers"
    "Acta Arithmetica 30(3), 241-252"
    "1976"
    "10.4064/aa-30-3-241-252"
    "https://doi.org/10.4064/aa-30-3-241-252"
    Source.academicArticleSource
    "foundational peer-reviewed stopping-time/density analysis for the accelerated 3x+1 process; historical coefficient/multiplicative stopping framework only"
    Source.publicAttribution

lagarias1985 : Source.AttributedSource
lagarias1985 =
  Source.mkDOISource
    "Jeffrey C. Lagarias"
    "The 3x + 1 Problem and its Generalizations"
    "The American Mathematical Monthly 92(1), 3-23"
    "1985"
    "10.1080/00029890.1985.11971528"
    "https://doi.org/10.1080/00029890.1985.11971528"
    Source.academicArticleSource
    "peer-reviewed survey/source for the historical coefficient-stopping formulation and its status as an open intermediate conjectural route; survey authority does not create a proof"
    Source.publicAttribution

sterinWoods2020 : Source.AttributedSource
sterinWoods2020 =
  Source.mkDOISource
    "Tristan Sterin; Damien Woods"
    "The Collatz Process Embeds a Base Conversion Algorithm"
    "Reachability Problems 2020, Lecture Notes in Computer Science 12448, 131-147"
    "2020"
    "10.1007/978-3-030-61739-4_9"
    "https://doi.org/10.1007/978-3-030-61739-4_9"
    Source.academicArticleSource
    "peer-reviewed exact quasi-cellular-automaton representation: horizontal binary Collatz evolution, vertical ternary evolution, and embedded base-3 to base-2 conversion; representation/computation donor only"
    Source.publicAttribution

------------------------------------------------------------------------
-- Preprints.  Their formal role is deliberately kept distinct from the
-- peer-reviewed sources above.
------------------------------------------------------------------------

niu2026 : Source.AttributedSource
niu2026 =
  Source.mkNoDOISource
    "Tong Niu"
    "Parity vectors and paradoxical sequences in the accelerated Collatz map"
    "arXiv:2605.13886"
    "2026"
    "https://arxiv.org/abs/2605.13886"
    (Source.namedSourceKind "academic preprint")
    "preprint proving finitary parity-vector and bounded-length paradoxical-sequence results and reporting a continued-fraction/Stern-Brocot numerical observation; no universal-Collatz promotion"
    Source.publicAttribution

angeltveit2026 : Source.AttributedSource
angeltveit2026 =
  Source.mkNoDOISource
    "Vigleik Angeltveit"
    "An improved algorithm for checking the Collatz conjecture for all n < 2^N"
    "arXiv:2602.10466"
    "2026"
    "https://arxiv.org/abs/2602.10466"
    (Source.namedSourceKind "academic preprint")
    "preprint algorithmic verification improvement; useful as a certificate-generation donor, not theorem authority for unbounded starts"
    Source.publicAttribution

inselmann2024 : Source.AttributedSource
inselmann2024 =
  Source.mkNoDOISource
    "Manuel Inselmann"
    "An approximation of the Collatz map and a lower bound for the average total stopping time"
    "arXiv:2402.03276"
    "2024"
    "https://arxiv.org/abs/2402.03276"
    (Source.namedSourceKind "academic preprint")
    "preprint extending typical accelerated-Collatz approximation to the maximal stated logarithmic horizon alpha = 2/log(4/3); almost-all calibration only"
    Source.publicAttribution

winklerStoppingTree : Source.AttributedSource
winklerStoppingTree =
  Source.mkNoDOISource
    "Mike Winkler"
    "The Recursive Stopping Time Structure of the 3x+1 Function"
    "arXiv:1709.03385"
    "2017; current arXiv revision"
    "https://arxiv.org/abs/1709.03385"
    (Source.namedSourceKind "academic preprint")
    "preprint recursive congruence-class/tree description for finite stopping-time classes; finite structural donor only and not universal coefficient stopping"
    Source.publicAttribution

winklerSemiconvergent2026 : Source.AttributedSource
winklerSemiconvergent2026 =
  Source.mkNoDOISource
    "Mike Winkler"
    "Admissible qx+1 Sequences, Semiconvergents, and Rational Catalan Numbers"
    "arXiv:2609.22303"
    "2026"
    "https://arxiv.org/abs/2609.22303"
    (Source.namedSourceKind "academic preprint")
    "preprint theorem identifying equality orders in finite admissible qx+1 passage bounds with one-sided best approximants/convergents/semiconvergents of log_2(q); exact finite multiplicative-word donor, not affine-correction or universal-stopping authority"
    Source.publicAttribution

------------------------------------------------------------------------
-- Admissions and atlas.
------------------------------------------------------------------------

taoAdmission : CollatzSourceAdmission
taoAdmission =
  collatzSourceAdmission tao2022 almostAllSyracuseTransportRole peerReviewed

rozierTerracolAdmission : CollatzSourceAdmission
rozierTerracolAdmission =
  collatzSourceAdmission rozierTerracol2026 paradoxicalFiniteSequenceRole peerReviewed

niuAdmission : CollatzSourceAdmission
niuAdmission =
  collatzSourceAdmission niu2026 parityVectorDensityPreprintRole preprint

barinaAdmission : CollatzSourceAdmission
barinaAdmission =
  collatzSourceAdmission barina2025 finiteVerificationRole peerReviewed

angeltveitAdmission : CollatzSourceAdmission
angeltveitAdmission =
  collatzSourceAdmission angeltveit2026 verificationAlgorithmPreprintRole preprint

inselmannAdmission : CollatzSourceAdmission
inselmannAdmission =
  collatzSourceAdmission inselmann2024 maximalTypicalHorizonPreprintRole preprint

hercherAdmission : CollatzSourceAdmission
hercherAdmission =
  collatzSourceAdmission hercher2023 nontrivialCycleExclusionRole peerReviewedWithCorrigendum

terrasAdmission : CollatzSourceAdmission
terrasAdmission =
  collatzSourceAdmission terras1976 foundationalCoefficientStoppingRole peerReviewed

lagariasAdmission : CollatzSourceAdmission
lagariasAdmission =
  collatzSourceAdmission lagarias1985 coefficientStoppingSurveyRole peerReviewed

sterinWoodsAdmission : CollatzSourceAdmission
sterinWoodsAdmission =
  collatzSourceAdmission sterinWoods2020 binaryTernaryAutomatonRole peerReviewed

winklerStoppingTreeAdmission : CollatzSourceAdmission
winklerStoppingTreeAdmission =
  collatzSourceAdmission winklerStoppingTree coefficientStoppingTreePreprintRole preprint

winklerSemiconvergentAdmission : CollatzSourceAdmission
winklerSemiconvergentAdmission =
  collatzSourceAdmission winklerSemiconvergent2026 semiconvergentPassagePreprintRole preprint

collatzSOTA2026Atlas : Source.AttributedSourceAtlas
collatzSOTA2026Atlas =
  Source.mkSourceAtlas
    "Collatz/Syracuse terminal max-cut SOTA atlas"
    "DASHI.Analysis.CollatzSyracuseSOTA2026Exact"
    (tao2022 ∷ rozierTerracol2026 ∷ barina2025 ∷ hercher2023 ∷
     terras1976 ∷ lagarias1985 ∷ sterinWoods2020 ∷
     niu2026 ∷ angeltveit2026 ∷ inselmann2024 ∷
     winklerStoppingTree ∷ winklerSemiconvergent2026 ∷ [])
    "claim-relative sources for almost-all dynamics, paradoxical finite sequences, coefficient/stopping-time history, parity-vector density, finite verification, verification algorithms, typical horizons, cycle exclusion, binary/ternary process representation, recursive stopping classes, and finite semiconvergent passage orders"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record CollatzSOTA2026Boundary : Set where
  constructor collatzSOTA2026Boundary
  field
    attributedSourceAtlasPaid : Nat
    claimRelativeRolesPaid : Nat
    peerReviewedAndPreprintRolesSeparated : Nat
    paradoxicalLiteratureAttachedToAffineCorrectionFrontier : Nat
    finiteVerificationAttachedAsComputationOnly : Nat
    cycleExclusionKeptSeparateFromUniversalStopping : Nat
    coefficientStoppingHistoryAttributed : Nat
    binaryTernaryAutomatonRoleSeparated : Nat
    semiconvergentPassageTheoremRoleSeparated : Nat

    externalSourcesImportCollatzProof : Nat
    preprintObservationPromotedToTheorem : Nat
    finiteVerificationPromotedToUnboundedProof : Nat
    almostAllPromotedToAllStarts : Nat
    coefficientStoppingConjecturePromotedToProof : Nat
    binaryTernaryAutomatonPromotedToUniversalStopping : Nat
    semiconvergentPassagePromotedToAffineCorrectionEscape : Nat

canonicalCollatzSOTA2026Boundary : CollatzSOTA2026Boundary
canonicalCollatzSOTA2026Boundary =
  collatzSOTA2026Boundary
    1 1 1 1 1 1 1 1 1
    0 0 0 0 0 0 0
