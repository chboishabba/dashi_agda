module DASHI.Wikimedia.IbrahimMonster3BModernCharacterVerificationKernel20SnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact as Historical
import DASHI.Wikimedia.IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact as Gauge

------------------------------------------------------------------------
-- MODERN INDEPENDENT VERIFICATION OF THE CLASS-20 3B-NORMALIZER FACTOR
--
-- Breuer--Magaard--Wilson independently reconstruct the Monster character
-- table and, in the detailed reproducibility protocol, make the 3B-normalizer
-- ambiguity executable.  The protocol starts from the canonical CTblLib table
--
--   CharacterTable("3^(1+12):6.Suz.2")
--
-- and reduces the diagonal order-three factors to exactly
--
--   H / [1,19]     and     H / [1,20].
--
-- Section 6 then uses the independently reconstructed Monster degree-196883
-- character chi:
--
--   * the restriction of chi to H/[1,19] has NO irreducible decomposition;
--   * the restriction of chi to H/[1,20] DOES admit a decomposition;
--   * the second candidate is character-table equivalent to stored MN3B.
--
-- Appendix 9 separately reconstructs H from explicit permutation generators
-- (with a MAGMA table computation) and checks permutation equivalence to the
-- CTblLib H table used above.
--
-- Thus the modern route independently corroborates the HISTORICAL coordinate
-- paid by Barraclough--Wilson:
--
--   Monster 3B normalizer = H / [1,20].
--
-- This owner is source/evidence formalisation.  It does NOT claim that our
-- local GAP matcher has run, and it does not promote source execution into an
-- Agda-kernel execution receipt.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution: published paper and detailed executable protocol are kept
--    as distinct source roles.
------------------------------------------------------------------------

breuerMagaardWilsonPaper : Attribution.AttributedSource
breuerMagaardWilsonPaper = Attribution.mkDOISource
  "Thomas Breuer; Kay Magaard; Robert A. Wilson"
  "Verification of the conjugacy classes and ordinary character table of the Monster"
  "Journal of Algebra 703, 452-463"
  "2026 (available online 2025)"
  "10.1016/j.jalgebra.2025.09.034"
  "https://doi.org/10.1016/j.jalgebra.2025.09.034"
  Attribution.academicArticleSource
  "peer-reviewed modern independent verification of the Monster conjugacy classes and ordinary character table; publication-level source for the verification programme"
  Attribution.publicAttribution

breuerMagaardWilsonProtocol : Attribution.AttributedSource
breuerMagaardWilsonProtocol = Attribution.mkNoDOISource
  "Thomas Breuer; Kay Magaard; Robert A. Wilson"
  "Some steps in the verification of the ordinary character table of the Monster group"
  "CTblLib reproducibility protocol / arXiv:2412.09313"
  "2024"
  "https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/doc/ctblm.pdf"
  (Attribution.namedSourceKind "primary reproducibility protocol / executable GAP transcript")
  "detailed source for the explicit H/[1,19] versus H/[1,20] test, the degree-196883 restriction discriminator, and the independent reconstruction of H; no separate journal DOI asserted for this protocol"
  Attribution.publicAttribution

paperAttribution = Snowball.canonicalSourceRoleSnowballReceipt breuerMagaardWilsonPaper
protocolAttribution = Snowball.canonicalSourceRoleSnowballReceipt breuerMagaardWilsonProtocol

publishedPaperDOI : String
publishedPaperDOI = "10.1016/j.jalgebra.2025.09.034"

publishedPaperArxiv : String
publishedPaperArxiv = "2412.12182"

detailedProtocolArxiv : String
detailedProtocolArxiv = "2412.09313"

------------------------------------------------------------------------
-- 2. Exact modern source receipt.
------------------------------------------------------------------------

record ModernKernelTwentyVerification : Set where
  constructor modern-kernel-twenty-verification
  field
    mainTableIdentity : String
    firstCandidateKernelClass : Nat
    secondCandidateKernelClass : Nat
    firstCandidateRestrictionDecomposes : Bool
    secondCandidateRestrictionDecomposes : Bool
    secondCandidateEquivalentToStoredMN3B : Bool
    independentHReconstructionEquivalentToLibraryH : Bool
    selectedKernelClass : Nat
    agreesWithHistoricalSupplementClass : Bool
    localMatcherExecutionPaid : Bool
open ModernKernelTwentyVerification public

canonicalModernKernelTwentyVerification : ModernKernelTwentyVerification
canonicalModernKernelTwentyVerification = modern-kernel-twenty-verification
  "3^(1+12):6.Suz.2"
  19
  20
  false
  true
  true
  true
  20
  true
  false

modernKernelClass : Nat
modernKernelClass = selectedKernelClass canonicalModernKernelTwentyVerification

historicalKernelClass : Nat
historicalKernelClass =
  Historical.nonidentityKernelClassPosition Historical.canonicalPrimarySupplementKernelCoordinate

------------------------------------------------------------------------
-- 3. Snowball coordinates remain typed and non-promoting.
--
-- RWTH's catalogue assigns DDC 510 to the exact published article.  That is a
-- publication-level catalogue coordinate and is NOT silently substituted for
-- the more specific topic-level DDC coordinates used elsewhere in the repo.
------------------------------------------------------------------------

record ModernVerificationExternalCoordinates : Set where
  constructor modern-verification-external-coordinates
  field
    exactPublicationWikidataQid : String
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    exactPublicationDewey : String
    groupRepresentationTopicDewey : String
    finiteGroupTopicDewey : String
    oeisCoordinate : String
    oeisHasVerificationAuthority : Bool
open ModernVerificationExternalCoordinates public

canonicalModernVerificationExternalCoordinates : ModernVerificationExternalCoordinates
canonicalModernVerificationExternalCoordinates = modern-verification-external-coordinates
  "unresolved rather than guessed for the exact Breuer-Magaard-Wilson article"
  "Q1055807"
  "Q600043"
  "Q1057968"
  "510"
  "512.22"
  "512.23"
  "not applicable: selecting H/[1,20] is a character-restriction and quotient identity, not an integer-sequence fact"
  false

------------------------------------------------------------------------
-- 4. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data PublishedVerificationCreatesLocalGAPReceipt : Set where
data PublishedVerificationCreatesAgdaKernelReceipt : Set where
data DdcCreatesKernelIdentity : Set where
data QidCreatesKernelIdentity : Set where
data OeisCreatesKernelIdentity : Set where
data CandidateNumberCreatesMonsterOccurrence : Set where

publishedVerificationDoesNotCreateLocalGAPReceipt :
  PublishedVerificationCreatesLocalGAPReceipt → ⊥
publishedVerificationDoesNotCreateLocalGAPReceipt ()

publishedVerificationDoesNotCreateAgdaKernelReceipt :
  PublishedVerificationCreatesAgdaKernelReceipt → ⊥
publishedVerificationDoesNotCreateAgdaKernelReceipt ()

ddcDoesNotCreateKernelIdentity : DdcCreatesKernelIdentity → ⊥
ddcDoesNotCreateKernelIdentity ()

qidDoesNotCreateKernelIdentity : QidCreatesKernelIdentity → ⊥
qidDoesNotCreateKernelIdentity ()

oeisDoesNotCreateKernelIdentity : OeisCreatesKernelIdentity → ⊥
oeisDoesNotCreateKernelIdentity ()

candidateNumberDoesNotCreateMonsterOccurrence :
  CandidateNumberCreatesMonsterOccurrence → ⊥
candidateNumberDoesNotCreateMonsterOccurrence ()

------------------------------------------------------------------------
-- 5. Corrected frontier.
------------------------------------------------------------------------

record ModernKernelVerificationFrontier : Set where
  constructor modern-kernel-verification-frontier
  field
    peerReviewedPaperDOIPaid : Bool
    detailedProtocolIdentityPaid : Bool
    candidateNineteenSourcePaid : Bool
    candidateTwentySourcePaid : Bool
    candidateNineteenRejectedByCharacterRestriction : Bool
    candidateTwentyAcceptedByCharacterRestriction : Bool
    candidateTwentyEquivalentStoredMN3B : Bool
    independentHReconstructionPaid : Bool
    historicalClassTwentyAgreementPaid : Bool
    invariantDiagonalKernelSubgroupPaid : Bool
    absoluteDiagonalSignNameRequiredForTwelveSeventyEight : Bool
    localFullCharacterMatcherExecuted : Bool
    nextResidual : String
open ModernKernelVerificationFrontier public

currentModernKernelVerificationFrontier : ModernKernelVerificationFrontier
currentModernKernelVerificationFrontier = modern-kernel-verification-frontier
  true true true true true true true true true true
  false false
  "the historical class-20 quotient coordinate is independently corroborated by the modern Monster character-table reconstruction: H/[1,19] fails the degree-196883 restriction-decomposition test and H/[1,20] passes and is equivalent to stored MN3B. Do not carry the 19-vs-20 choice or the t1*t2-vs-t1*t2^-1 orientation label as remaining mathematical proof debt. The next mandatory payment is execution of the repo's full Suzuki/main quotient same-object matcher, which must identify the 12a/b and 78a/b pair-family constituents in the actual restricted Monster character; source verification does not create that local execution receipt."

historicalFrontier : Historical.PrimarySupplementKernelFrontier
historicalFrontier = Historical.currentPrimarySupplementKernelFrontier

gaugeFrontier : Gauge.DiagonalKernelGaugeCorrectionFrontier
gaugeFrontier = Gauge.currentDiagonalKernelGaugeCorrectionFrontier
