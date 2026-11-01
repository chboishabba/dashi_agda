module DASHI.Wikimedia.IbrahimMonster3BT1WordT2ScalarRoutingSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BDiagonalC3QuotientOrientationSnowballExact as Orientation
import DASHI.Wikimedia.IbrahimMonster3BFactorCQuotientWordSnowballExact as Factor

------------------------------------------------------------------------
-- LITERAL t1 WORD + SOURCE-NATIVE t2 ROUTING
--
-- Bray--Wilson's explicit GF(3) construction pays one diagonal factor much
-- more strongly than a symbolic name:
--
--   t1 = [ C , D C D ]^7
--
-- generates the normal subgroup of order three in 3.Suz:2 (and hence fixes
-- the Suzuki-side C3 coordinate used in the central-product test).
--
-- The second factor t2 is the central C3 of the extraspecial 3^(1+12) side.
-- Barraclough's thesis inventories the concrete source route used to represent
-- that side:
--
--   1+12+1/BCE.sh
--   38/
--   V6s2/pasting39.case.mag
--   V6s2/pasting37functions.mag
--   V6s2/makewords.mag
--
-- and separately /monster/mop7/factor.c for the quotient generator.
--
-- We therefore no longer treat both diagonal factors as abstract unknowns.
-- t1's literal standard-generator word is paid.  t2's subgroup role is paid,
-- but the exact matrix/scalar element aligned with the historical q word is
-- still a producer obligation.
------------------------------------------------------------------------

brayWilson : Attribution.AttributedSource
brayWilson = Attribution.mkDOISource
  "John N. Bray; Robert A. Wilson"
  "Explicit representations of maximal subgroups of the Monster"
  "Journal of Algebra 300(2), 834-857"
  "2006"
  "10.1016/j.jalgebra.2005.12.017"
  "https://doi.org/10.1016/j.jalgebra.2005.12.017"
  Attribution.academicArticleSource
  "primary source for t1=[C,DCD]^7, the two diagonal C3 quotient alternatives, the arbitrary modular 12+/- labelling convention, and the corrected discriminator word J"
  Attribution.publicAttribution

barracloughThesis : Attribution.AttributedSource
barracloughThesis = Attribution.mkNoDOISource
  "Richard William Barraclough"
  "Some Calculations Related To The Monster Group"
  "PhD thesis, University of Birmingham"
  "2005"
  "https://webspace.maths.qmul.ac.uk/r.a.wilson/RWBphd.pdf"
  (Attribution.namedSourceKind "doctoral thesis / computational archive inventory")
  "primary source for the 1+12+1, 38 and V6s2 program routes used to construct matrices, power maps and quotient maps, and for the /monster/mop7/factor.c artifact identity; no thesis DOI asserted"
  Attribution.publicAttribution

brayWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt brayWilson
thesisAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughThesis

record LiteralCentralGeneratorReceipt : Set where
  constructor literal-central-generator-receipt
  field
    actor : String
    generatorName : String
    sourceWord : String
    subgroupRole : String
    literalWordPaid : Bool
open LiteralCentralGeneratorReceipt public

suzukiT1Receipt : LiteralCentralGeneratorReceipt
suzukiT1Receipt = literal-central-generator-receipt
  "3.Suz:2 / 6.Suz:2 central cover coordinate"
  "t1"
  "[C,DCD]^7"
  "generator of the normal cyclic subgroup of order 3 on the Suzuki side"
  true

record ExtraspecialT2Routing : Set where
  constructor extraspecial-t2-routing
  field
    generatorName : String
    subgroupRole : String
    centralSubgroupIdentityPaid : Bool
    exactMatrixElementPaid : Bool
    exactScalarOrientationPaid : Bool
    historicalQWordAlignmentPaid : Bool
    constructionRoute : String
open ExtraspecialT2Routing public

extraspecialT2Routing : ExtraspecialT2Routing
extraspecialT2Routing = extraspecial-t2-routing
  "t2"
  "central C3 in the extraspecial 3^(1+12) side"
  true
  false
  false
  false
  "Barraclough thesis: 1+12+1/BCE.sh -> 38/ -> V6s2/pasting39.case.mag and pasting37functions.mag; makewords.mag emits main-table class SLPs; /monster/mop7/factor.c produces the quotient-kernel generator"

correctedJWord : String
correctedJWord = "((zeta^2 gamma)^4 zeta)^-1 zeta (zeta^2 gamma)^4"

record HistoricalProgramRoute : Set where
  constructor historical-program-route
  field
    bceScript : String
    thirtyEightDirectory : String
    mainPastingProgram : String
    matrixConstructionFunctions : String
    classWordProducer : String
    quotientGeneratorProducer : String
    exactBytesRecovered : Bool
open HistoricalProgramRoute public

canonicalHistoricalProgramRoute : HistoricalProgramRoute
canonicalHistoricalProgramRoute = historical-program-route
  "1+12+1/BCE.sh"
  "38/"
  "V6s2/pasting39.case.mag"
  "V6s2/pasting37functions.mag"
  "V6s2/makewords.mag"
  "/monster/mop7/factor.c"
  false

------------------------------------------------------------------------
-- Attribution/navigation coordinates remain typed and non-promoting.
------------------------------------------------------------------------

record GeneratorWordExternalCoordinates : Set where
  constructor generator-word-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    exactPaperQid : String
    oeisCoordinate : String
    oeisHasGeneratorWordAuthority : Bool
open GeneratorWordExternalCoordinates public

canonicalGeneratorWordExternalCoordinates : GeneratorWordExternalCoordinates
canonicalGeneratorWordExternalCoordinates = generator-word-external-coordinates
  "Q1055807"
  "Q1057968"
  "512.22"
  "512.23"
  "unresolved rather than guessed for the exact Bray-Wilson article"
  "not applicable: standard-generator words and diagonal quotient kernels are not integer-sequence objects"
  false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data T1WordCreatesT2Element : Set where
data T2SubgroupRoleCreatesMatrix : Set where
data ProgramPathCreatesProgramBytes : Set where
data CorrectedJWordCreatesKernelIdentity : Set where
data ModularTwelveSignCreatesComplexAtlasLabel : Set where

literalT1DoesNotCreateT2 : T1WordCreatesT2Element → ⊥
literalT1DoesNotCreateT2 ()

t2RoleDoesNotCreateMatrix : T2SubgroupRoleCreatesMatrix → ⊥
t2RoleDoesNotCreateMatrix ()

programPathDoesNotCreateBytes : ProgramPathCreatesProgramBytes → ⊥
programPathDoesNotCreateBytes ()

jWordDoesNotCreateKernelIdentityWithoutEvaluation : CorrectedJWordCreatesKernelIdentity → ⊥
jWordDoesNotCreateKernelIdentityWithoutEvaluation ()

modularSignDoesNotCreateComplexLabel : ModularTwelveSignCreatesComplexAtlasLabel → ⊥
modularSignDoesNotCreateComplexLabel ()

------------------------------------------------------------------------
-- Highest-alpha residual.
------------------------------------------------------------------------

record T1T2RoutingFrontier : Set where
  constructor t1-t2-routing-frontier
  field
    brayWilsonDOIPaid : Bool
    t1LiteralWordPaid : Bool
    t2CentralSubgroupRolePaid : Bool
    correctedJWordPaid : Bool
    thesisConstructionRoutePaid : Bool
    factorCArtifactIdentityPaid : Bool
    historicalProgramBytesPaid : Bool
    t2ExactMatrixPaid : Bool
    qWordPaid : Bool
    qWordClassTwentyWeldPaid : Bool
    exactDiagonalKernelCorrelationPaid : Bool
    nextResidual : String
open T1T2RoutingFrontier public

currentT1T2RoutingFrontier : T1T2RoutingFrontier
currentT1T2RoutingFrontier = t1-t2-routing-frontier
  true true true true true true
  false false false false false
  "recover either the historical V6s2/38 program bytes sufficient to instantiate the extraspecial central element t2, or /monster/mop7/factor.c / the exact quotient word q(C,D,E). Then evaluate the source-paid literal t1=[C,DCD]^7 and the recovered t2/q in the same compatible representation, weld the quotient generator to primary supplement main-table class 20, and only then classify the killed diagonal as <t1*t2> or <t1*t2^-1>. The corrected J word is a discriminator input, not a proof until evaluated."

orientationFrontier : Orientation.DiagonalOrientationFrontier
orientationFrontier = Orientation.currentDiagonalOrientationFrontier

factorFrontier : Factor.QuotientWordFrontier
factorFrontier = Factor.currentQuotientWordFrontier
