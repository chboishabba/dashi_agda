module DASHI.Analysis.CollatzSyracuseSOTA2026Exact where

------------------------------------------------------------------------
-- ATTRIBUTION-SAFE COLLATZ / SYRACUSE SOTA ATLAS
--
-- This owner records external source identity and the bounded role for which
-- each source is relevant to the current DASHI Collatz max-cut.  It does NOT
-- import an external theorem into Agda and does NOT promote almost-all,
-- finite-verification, cycle-exclusion, or parity-vector results to the
-- universal Collatz conjecture.
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

collatzSOTA2026Atlas : Source.AttributedSourceAtlas
collatzSOTA2026Atlas =
  Source.mkSourceAtlas
    "Collatz/Syracuse terminal max-cut SOTA atlas"
    "DASHI.Analysis.CollatzSyracuseSOTA2026Exact"
    (tao2022 ∷ rozierTerracol2026 ∷ barina2025 ∷ hercher2023 ∷
     niu2026 ∷ angeltveit2026 ∷ inselmann2024 ∷ [])
    "claim-relative sources for almost-all dynamics, paradoxical finite sequences, parity-vector density, finite verification, verification algorithms, typical horizons, and cycle exclusion"

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

    externalSourcesImportCollatzProof : Nat
    preprintObservationPromotedToTheorem : Nat
    finiteVerificationPromotedToUnboundedProof : Nat
    almostAllPromotedToAllStarts : Nat

canonicalCollatzSOTA2026Boundary : CollatzSOTA2026Boundary
canonicalCollatzSOTA2026Boundary =
  collatzSOTA2026Boundary
    1 1 1 1 1 1
    0 0 0 0
