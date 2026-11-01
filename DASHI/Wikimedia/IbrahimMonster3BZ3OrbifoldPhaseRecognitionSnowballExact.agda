module DASHI.Wikimedia.IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- PRIMARY Z3-ORBIFOLD PHASE SOURCE FOR THE MONSTER 3B RECOGNITION LANE
--
-- Chen--Lam--Shimakura construct the holomorphic VOA V# as a Z3-graded simple
-- current extension associated to an order-three Leech-lattice automorphism.
-- They prove V# is isomorphic to the Moonshine VOA and that its full
-- automorphism group is the Monster.  Their construction also provides a
-- natural order-three automorphism acting by the three cyclotomic phases on
-- the three grading summands and describes the associated maximal 3-local
-- subgroup of shape 3^(1+12).2.Suz:2.
--
-- This is exactly the kind of source needed to pay PHASE-RESOLVED VOA
-- structure.  It is deliberately not promoted to the repo's stronger
-- ActualZetaSectorRecognition, which additionally requires a concrete
-- two-sided chart to ZetaModelBasis = X6 x Fin 90 plus all translation and
-- modulation intertwiners.
------------------------------------------------------------------------

chenLamShimakura : Attribution.AttributedSource
chenLamShimakura = Attribution.mkDOISource
  "Hsian-Yang Chen; Ching Hung Lam; Hiroki Shimakura"
  "Z_3-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster"
  "Mathematische Zeitschrift 288, 75-100"
  "2018 (online 2017)"
  "10.1007/s00209-017-1878-z"
  "https://doi.org/10.1007/s00209-017-1878-z"
  Attribution.academicArticleSource
  "primary source for the Z3-graded Moonshine-VOA construction, phase action, Monster automorphism-group identification, and maximal 3-local subgroup structure; not a source for DASHI's X6 x Fin90 basis chart"
  Attribution.publicAttribution

chenLamShimakuraAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt chenLamShimakura

arxivCoordinate : String
arxivCoordinate = "1606.05961"

------------------------------------------------------------------------
-- 1. Exact source payments retained as a typed receipt.
------------------------------------------------------------------------

record Z3OrbifoldPhaseReceipt : Set where
  constructor z3-orbifold-phase-receipt
  field
    orbifoldVOAName : String
    fixedSummand : String
    firstTwistedIntegralSummand : String
    secondTwistedIntegralSummand : String
    phaseAutomorphismName : String
    firstPhase : String
    secondPhase : String
    thirdPhase : String
    threeSummandZ3GradingPaid : Bool
    phaseEigenvaluesOneXiXiSquaredPaid : Bool
    moonshineVOAIsomorphismPaid : Bool
    fullAutomorphismGroupMonsterPaid : Bool
    threeLocalShape : String
    threeLocalShapePaid : Bool
open Z3OrbifoldPhaseReceipt public

canonicalZ3OrbifoldPhaseReceipt : Z3OrbifoldPhaseReceipt
canonicalZ3OrbifoldPhaseReceipt = z3-orbifold-phase-receipt
  "V#"
  "V_Lambda^tau"
  "(V_Lambda^{T1}(tau))_Z"
  "(V_Lambda^{T2}(tau^2))_Z"
  "f / tau-prime grading automorphism"
  "1"
  "xi"
  "xi^2"
  true true true true
  "3^(1+12).2.Suz:2"
  true

------------------------------------------------------------------------
-- 2. Recognition WrongType firewall.
------------------------------------------------------------------------

data SourceCreatesZetaModelBasisChart : Set where
data SourceCreatesTranslationIntertwiners : Set where
data SourceCreatesModulationIntertwiners : Set where
data Z3GradingCreatesSelectedMonster3BClassIdentity : Set where
data ThreeLocalShapeCreatesLiteralSelectedElementEquality : Set where
data QidCreatesRecognition : Set where
data DeweyCreatesRecognition : Set where
data OeisCreatesRecognition : Set where

sourceDoesNotCreateZetaModelBasisChart :
  SourceCreatesZetaModelBasisChart → ⊥
sourceDoesNotCreateZetaModelBasisChart ()

sourceDoesNotCreateTranslationIntertwiners :
  SourceCreatesTranslationIntertwiners → ⊥
sourceDoesNotCreateTranslationIntertwiners ()

sourceDoesNotCreateModulationIntertwiners :
  SourceCreatesModulationIntertwiners → ⊥
sourceDoesNotCreateModulationIntertwiners ()

z3GradingDoesNotCreateSelectedMonster3BClassIdentity :
  Z3GradingCreatesSelectedMonster3BClassIdentity → ⊥
z3GradingDoesNotCreateSelectedMonster3BClassIdentity ()

threeLocalShapeDoesNotCreateLiteralSelectedElementEquality :
  ThreeLocalShapeCreatesLiteralSelectedElementEquality → ⊥
threeLocalShapeDoesNotCreateLiteralSelectedElementEquality ()

qidDoesNotCreateRecognition : QidCreatesRecognition → ⊥
qidDoesNotCreateRecognition ()

deweyDoesNotCreateRecognition : DeweyCreatesRecognition → ⊥
deweyDoesNotCreateRecognition ()

oeisDoesNotCreateRecognition : OeisCreatesRecognition → ⊥
oeisDoesNotCreateRecognition ()

------------------------------------------------------------------------
-- 3. DOI / QID / Dewey / OEIS coordinates remain role-separated.
------------------------------------------------------------------------

record Z3OrbifoldExternalCoordinates : Set where
  constructor z3-orbifold-external-coordinates
  field
    exactArticleQid : String
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    exactPublicationDewey : String
    groupRepresentationTopicDewey : String
    finiteGroupTopicDewey : String
    oeisCoordinate : String
    oeisHasRecognitionAuthority : Bool
open Z3OrbifoldExternalCoordinates public

canonicalZ3OrbifoldExternalCoordinates : Z3OrbifoldExternalCoordinates
canonicalZ3OrbifoldExternalCoordinates = z3-orbifold-external-coordinates
  "unresolved rather than guessed for the exact Chen-Lam-Shimakura article"
  "Q1055807"
  "Q600043"
  "Q1057968"
  "unresolved rather than inferred from topic classification"
  "512.22"
  "512.23"
  "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no Z3-orbifold, eigenspace, basis-chart, translation, modulation, or recognition authority"
  false

------------------------------------------------------------------------
-- 4. Pareto frontier after source acquisition.
------------------------------------------------------------------------

record Z3OrbifoldRecognitionFrontier : Set where
  constructor z3-orbifold-recognition-frontier
  field
    primaryDOIPaid : Bool
    arxivIdentityPaid : Bool
    explicitThreeSummandGradingPaid : Bool
    explicitCyclotomicPhaseActionPaid : Bool
    moonshineVOAIdentificationPaid : Bool
    monsterAutomorphismGroupPaid : Bool
    threeLocalSubgroupStructurePaid : Bool
    repoLiteralSelectedElementSameObjectPaid : Bool
    actualZetaModelBasisChartPaid : Bool
    sixTranslationIntertwinersPaid : Bool
    sixModulationIntertwinersPaid : Bool
    actualZetaSectorRecognitionPaid : Bool
    nextResidual : String
open Z3OrbifoldRecognitionFrontier public

currentZ3OrbifoldRecognitionFrontier : Z3OrbifoldRecognitionFrontier
currentZ3OrbifoldRecognitionFrontier = z3-orbifold-recognition-frontier
  true true true true true true true
  false false false false false
  "use the Chen-Lam-Shimakura Z3-graded Moonshine construction as source authority for a genuine phase-resolved linear VOA sector and the associated 3-local Monster subgroup, but keep the repo-specific same-object weld explicit. The next recognition payment is still constructive: identify the repo's selected central-zeta literal sector with the appropriate source eigenspace, then build an actual two-sided chart from that sector to ZetaModelBasis = X6 x Fin90 and prove the six translation and six modulation intertwiners. The source's Z3 grading, Monster identification, DOI/QID/Dewey/OEIS coordinates, and 3-local group shape do not manufacture this chart."
