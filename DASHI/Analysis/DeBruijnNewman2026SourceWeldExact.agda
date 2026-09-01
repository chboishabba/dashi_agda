module DASHI.Analysis.DeBruijnNewman2026SourceWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.DeBruijnNewman2026ClaimAuditExact as Claim

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION / BOUNDARY
--
-- Published analytic source:
--   D. H. J. Polymath,
--   "Effective approximation of heat flow evolution of the Riemann xi
--   function, and a new upper bound for the de Bruijn-Newman constant",
--   Research in the Mathematical Sciences 6 (2019).
--   DOI: 10.1007/s40687-019-0193-1
--   arXiv:1904.12438.
--
-- Verified-zero-height source:
--   Dave Platt and Tim Trudgian,
--   "The Riemann hypothesis is true up to 3*10^12",
--   Bulletin of the London Mathematical Society 53 (2021), 792--797.
--   DOI: 10.1112/blms.12460.
--
-- 2026 candidate/certificate source:
--   Jude Gomila, dbn-lambda-01787854-candidate-audit, public audit repository,
--   candidate bound Lambda <= 0.1787854.  The public source labels the result
--   as computer-assisted and not peer reviewed.  Repository/release evidence
--   is kept as candidate provenance, not publication authority.
--
-- This module is a DASHI source-weld reconstruction.  It does not attribute
-- the typed BIDI graph to any source author and it does not replay the external
-- interval certificates inside Agda.
------------------------------------------------------------------------

data DBNSource : Set where
  polymath2019 : DBNSource
  plattTrudgian2021 : DBNSource
  gomila2026Candidate : DBNSource

sourceAuthor : DBNSource → String
sourceAuthor polymath2019 = "D. H. J. Polymath"
sourceAuthor plattTrudgian2021 = "Dave Platt; Tim Trudgian"
sourceAuthor gomila2026Candidate = "Jude Gomila"

sourceIdentifier : DBNSource → String
sourceIdentifier polymath2019 = "doi:10.1007/s40687-019-0193-1; arXiv:1904.12438"
sourceIdentifier plattTrudgian2021 = "doi:10.1112/blms.12460"
sourceIdentifier gomila2026Candidate = "https://github.com/judegomila/dbn-lambda-01787854-candidate-audit"

------------------------------------------------------------------------
-- The BIDI consumer is the published criterion; its premises must be supplied
-- by the same declared parameter/certificate package rather than by parallel
-- numerical objects with matching prose labels.
------------------------------------------------------------------------

data CriterionObligation : Set where
  verifiedZeroHeight : CriterionObligation
  finalTimeRightHalfLine : CriterionObligation
  intermediateTimeBarrier : CriterionObligation
  exactParameterCompatibility : CriterionObligation

data SupplierKind : Set where
  publishedTheoremSupplier : SupplierKind
  publishedVerifiedComputation : SupplierKind
  candidateIntervalCertificate : SupplierKind
  candidateParameterIdentity : SupplierKind

data VerificationLayer : Set where
  sourceStatementRecovered : VerificationLayer
  externalReplayReported : VerificationLayer
  independentlyReplayed : VerificationLayer
  reconstructedInAgda : VerificationLayer
  peerReviewedPublication : VerificationLayer

record CriterionSupplier : Set where
  constructor supplier
  field
    obligation : CriterionObligation
    source : DBNSource
    kind : SupplierKind
    layer : VerificationLayer
    locator : String

open CriterionSupplier public

verifiedHeightSupplier : CriterionSupplier
verifiedHeightSupplier =
  supplier verifiedZeroHeight plattTrudgian2021 publishedVerifiedComputation
    sourceStatementRecovered
    "Platt-Trudgian verified-height theorem; candidate audit consumes the published height"

finalTimeSupplier : CriterionSupplier
finalTimeSupplier =
  supplier finalTimeRightHalfLine gomila2026Candidate candidateIntervalCertificate
    externalReplayReported
    "candidate final-time right-half-line interval certificate package"

barrierSupplier : CriterionSupplier
barrierSupplier =
  supplier intermediateTimeBarrier gomila2026Candidate candidateIntervalCertificate
    externalReplayReported
    "candidate intermediate-time barrier interval certificate package"

parameterSupplier : CriterionSupplier
parameterSupplier =
  supplier exactParameterCompatibility gomila2026Candidate candidateParameterIdentity
    sourceStatementRecovered
    "t0=129/800; y0^2=87677/2500000; B=893927/5000000"

------------------------------------------------------------------------
-- Exact candidate parameters are reused from the merged claim owner rather
-- than duplicated as a second arithmetic object.
------------------------------------------------------------------------

t0 = Claim.t0
y0Squared = Claim.y0Squared
claimedUpperBound = Claim.claimedUpperBound
parameterArithmeticExact = Claim.parameterArithmeticExact

candidateX : Nat
candidateX = 6000000185827

plattTrudgianVerifiedHeight : Nat
plattTrudgianVerifiedHeight = 3000175332800

-- The public proof note reports that X/2 lies below the published verified
-- height, with doubled surplus 350479773.  This datum is provenance only here;
-- the inequality proof is not silently reconstructed from a decimal statement.
reportedDoubledHeightSurplus : Nat
reportedDoubledHeightSurplus = 350479773

------------------------------------------------------------------------
-- Promotion gate.  Published theorem statement, same-parameter instantiation,
-- exact certificate replay, and theorem application are different receipts.
------------------------------------------------------------------------

record DBNSourceWeld : Set where
  field
    criterionSource : DBNSource
    criterionExactStatement : Set
    heightSupplier : CriterionSupplier
    finalSupplier : CriterionSupplier
    barrierSupplier : CriterionSupplier
    parameterCompatibility : CriterionSupplier
    sameParameterPackage : Set
    certificateReplayReceipt : Set
    criterionApplicationProof : Set

-- No constructor from a candidate source bundle alone is supplied.

data CandidateStatus : Set where
  candidatePublic : CandidateStatus
  certificatePackageReported : CandidateStatus
  agdaCertificateReplay : CandidateStatus
  establishedPublishedResult : CandidateStatus

publicCandidateNotAgdaReplay : candidatePublic ≡ agdaCertificateReplay → ⊥
publicCandidateNotAgdaReplay ()

reportedPackageNotPublishedResult :
  certificatePackageReported ≡ establishedPublishedResult → ⊥
reportedPackageNotPublishedResult ()

------------------------------------------------------------------------
-- Current cut.
------------------------------------------------------------------------

polymathCriterionSourceRecovered : Bool
polymathCriterionSourceRecovered = true

plattTrudgianSourceRecovered : Bool
plattTrudgianSourceRecovered = true

candidateParametersRecovered : Bool
candidateParametersRecovered = true

candidateCertificateArchitectureRecovered : Bool
candidateCertificateArchitectureRecovered = true

candidateCertificateReplayOwnedInAgda : Bool
candidateCertificateReplayOwnedInAgda = false

criterionApplicationReconstructedInAgda : Bool
criterionApplicationReconstructedInAgda = false

candidatePeerReviewed : Bool
candidatePeerReviewed = false

candidateCertificateReplayOwnedInAgdaIsFalse :
  candidateCertificateReplayOwnedInAgda ≡ false
candidateCertificateReplayOwnedInAgdaIsFalse = refl

criterionApplicationReconstructedInAgdaIsFalse :
  criterionApplicationReconstructedInAgda ≡ false
criterionApplicationReconstructedInAgdaIsFalse = refl
