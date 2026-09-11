module DASHI.Wikimedia.IbrahimMonster3BFactorCQuotientWordSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact as Supplement
import DASHI.Wikimedia.IbrahimMonster3BDiagonalC3QuotientOrientationSnowballExact as Orientation

------------------------------------------------------------------------
-- HISTORICAL QUOTIENT-WORD / factor.c SNOWBALL
--
-- Barraclough--Wilson explicitly keep the generators C,D,E of the main
-- 3^1+12:6.Suz:2 construction aligned with Linton--Parker--Walsh--Wilson's
-- computer construction.  They state that the earlier construction supplies
-- a word q in the order-three subgroup which must be factored out to obtain
-- N(3B).  Barraclough's thesis appendix independently inventories
--
--   /monster/mop7/factor.c
--
-- with the role "produces a generator for the 3-group that must be factored
-- out ... to obtain N(3B)".
--
-- This is the strongest current acquisition target for the remaining diagonal
-- kernel identity.  The present owner records the producer/custody chain; it
-- does NOT invent the missing word q or claim recovery of factor.c bytes.
------------------------------------------------------------------------

lintonParkerWalshWilson : Attribution.AttributedSource
lintonParkerWalshWilson = Attribution.mkDOISource
  "S. A. Linton; R. A. Parker; P. G. Walsh; R. A. Wilson"
  "Computer construction of the Monster"
  "Journal of Group Theory 1(4), 307-337"
  "1998"
  "10.1515/jgth.1998.023"
  "https://doi.org/10.1515/jgth.1998.023"
  Attribution.academicArticleSource
  "primary construction source whose C,D,E-compatible model supplies the quotient-kernel word used by the later N(3B) character-table computation"
  Attribution.publicAttribution

barracloughThesis : Attribution.AttributedSource
barracloughThesis = Attribution.mkNoDOISource
  "Richard William Barraclough"
  "Some Calculations Related To The Monster Group"
  "PhD thesis, University of Birmingham"
  "2005"
  "https://webspace.maths.qmul.ac.uk/r.a.wilson/RWBphd.pdf"
  (Attribution.namedSourceKind "doctoral thesis / computational archive inventory")
  "primary provenance for the /monster/mop7/factor.c artifact identity and its stated role; no thesis DOI asserted"
  Attribution.publicAttribution

lintonAttribution = Snowball.canonicalSourceRoleSnowballReceipt lintonParkerWalshWilson
thesisAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughThesis

constructionDOI : String
constructionDOI = "10.1515/jgth.1998.023"

record QuotientWordCustodyChain : Set where
  constructor quotient-word-custody-chain
  field
    earlierConstructionUsesCompatibleCDE : Bool
    laterCharacterTableKeepsCompatibleCDE : Bool
    earlierConstructionSuppliesQuotientWordQ : Bool
    thesisNamesFactorCArtifact : Bool
    factorCStatedToProduceQuotientGenerator : Bool
    primarySupplementPaysClassTwentyCoordinate : Bool
    exactFactorCBytesLocated : Bool
    exactQuotientWordLocated : Bool
    exactWordEvaluationReceiptLocated : Bool
open QuotientWordCustodyChain public

canonicalQuotientWordCustodyChain : QuotientWordCustodyChain
canonicalQuotientWordCustodyChain = quotient-word-custody-chain
  true true true true true true
  false false false

------------------------------------------------------------------------
-- External coordinates: typed navigation only.
------------------------------------------------------------------------

record QuotientWordExternalCoordinates : Set where
  constructor quotient-word-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    exactConstructionQid : String
    oeisCoordinate : String
    oeisHasWordAuthority : Bool
open QuotientWordExternalCoordinates public

canonicalQuotientWordExternalCoordinates : QuotientWordExternalCoordinates
canonicalQuotientWordExternalCoordinates = quotient-word-external-coordinates
  "Q1055807"
  "Q1057968"
  "512.22"
  "512.23"
  "unresolved rather than guessed for the exact 1998 construction object"
  "not applicable: a quotient word in C,D,E is not an integer-sequence coordinate"
  false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data ArtifactNameCreatesArtifactBytes : Set where
data ArtifactRoleCreatesQuotientWord : Set where
data CompatibleGeneratorNamesCreateSameWord : Set where
data ClassTwentyCreatesWordQ : Set where
data DOIImportsExecutableArtifact : Set where
data QidImportsExecutableArtifact : Set where
data DeweyImportsExecutableArtifact : Set where
data OeisImportsExecutableArtifact : Set where

artifactNameDoesNotCreateBytes : ArtifactNameCreatesArtifactBytes → ⊥
artifactNameDoesNotCreateBytes ()

artifactRoleDoesNotCreateWord : ArtifactRoleCreatesQuotientWord → ⊥
artifactRoleDoesNotCreateWord ()

compatibleNamesDoNotCreateWord : CompatibleGeneratorNamesCreateSameWord → ⊥
compatibleNamesDoNotCreateWord ()

classTwentyDoesNotCreateWord : ClassTwentyCreatesWordQ → ⊥
classTwentyDoesNotCreateWord ()

doiDoesNotImportArtifact : DOIImportsExecutableArtifact → ⊥
doiDoesNotImportArtifact ()

qidDoesNotImportArtifact : QidImportsExecutableArtifact → ⊥
qidDoesNotImportArtifact ()

deweyDoesNotImportArtifact : DeweyImportsExecutableArtifact → ⊥
deweyDoesNotImportArtifact ()

oeisDoesNotImportArtifact : OeisImportsExecutableArtifact → ⊥
oeisDoesNotImportArtifact ()

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record QuotientWordFrontier : Set where
  constructor quotient-word-frontier
  field
    constructionPaperIdentityPaid : Bool
    constructionPaperDOIPaid : Bool
    sameCDECompatibilitySourcePaid : Bool
    quotientWordQExistenceSourcePaid : Bool
    factorCPathIdentitySourcePaid : Bool
    factorCRoleSourcePaid : Bool
    primarySupplementClassTwentyPaid : Bool
    factorCBytesPaid : Bool
    quotientWordQPaid : Bool
    wordQMapsToClassTwentyPaid : Bool
    wordQIdentifiesBrayWilsonDiagonalPaid : Bool
    nextResidual : String
open QuotientWordFrontier public

currentQuotientWordFrontier : QuotientWordFrontier
currentQuotientWordFrontier = quotient-word-frontier
  true true true true true true true
  false false false false
  "acquire the historical /monster/mop7/factor.c bytes or the exact quotient word q(C,D,E) supplied by the Linton-Parker-Walsh-Wilson construction. Then evaluate that same word in the compatible main-table/explicit-representation generators and weld its conjugacy class to primary supplement class 20. Finally crosswalk that concrete kernel generator to Bray-Wilson's <t1*t2> versus <t1*t2^-1> diagonal test. Do not manufacture q from class 20, the artifact pathname, DOI/QID/Dewey/OEIS, or generator-name compatibility alone."

supplementFrontier : Supplement.PrimarySupplementKernelFrontier
supplementFrontier = Supplement.currentPrimarySupplementKernelFrontier

orientationFrontier : Orientation.DiagonalOrientationFrontier
orientationFrontier = Orientation.currentDiagonalOrientationFrontier
