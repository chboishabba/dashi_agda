module DASHI.Wikimedia.IbrahimMonster3BLinearShortestFrontierCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Base369Monster3BShortestFrontierCapstoneBidiExact as Historical
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact as NoGo
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as Character
import DASHI.Wikimedia.IbrahimMonsterCharacterToTwoIsotypicBlocksMathlibSnowballExact as Isotypic

------------------------------------------------------------------------
-- CORRECTED SHORTEST FRONTIER AFTER THE BASIS/LINEAR WRONGTYPE AUDIT
--
-- The historical capstone remains a valid compiler for a recognized finite
-- Schrödinger BASIS chart:
--
--   W_zeta(set) <-> X6 x Fin 90
--
-- and therefore for the ninety Base369 appraisal slices.  What it cannot do is
-- turn `Fin 90` into the ninety-dimensional multiplicity VECTOR SPACE carrying
-- the inertia representation.
--
-- The source-paid 12+78 Suzuki character makes this distinction decisive: its
-- value on the relevant central order-three element is nonintegral, whereas a
-- pure permutation action on ninety labels has a natural-number fixed-point
-- character.  Thus the old `Inertia -> Fin90 -> Fin90` target is not merely
-- unpaid; it is the wrong representation type for the source-paid action.
--
-- The corrected mandatory route is therefore:
--
--   same literal selected 3B action
--     -> linear structure on its literal zeta eigenspace W_zeta
--     -> S_zeta = Hom_E(H_zeta,W_zeta)
--     -> actual inverse-cocycle inertia action on S_zeta
--     -> source-paid chi_12 + chi_78
--     -> generic semisimple/isotypic compiler
--     -> actual equivariant S_12 + S_78 decomposition.
--
-- The finite chart remains useful in parallel for basis/projector/appraisal
-- computations and is not deleted or retroactively declared wrong.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Primary/source attribution retained at the corrected cut.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary source for the 3B normalizer character construction and the 12+78 multiplicity representation; not authority for identifying a 90-point basis permutation"
  Attribution.publicAttribution

serre : Attribution.AttributedSource
serre = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicArticleSource
  "standard representation-theory calibration for linear, projective, tensor and permutation representations"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 2. The corrected capstone source keeps both routes but assigns them their
--    proper roles.
------------------------------------------------------------------------

record LinearShortest3BFrontierSource (Monster K : Set) : Set₁ where
  field
    -- Historical finite-basis/appraisal compiler on the exact old source.
    historicalFiniteBasisCapstone : Historical.Shortest3BFrontierSource Monster K

    -- Mandatory linear theorem route.
    linearZetaSector : LinearZeta.LinearSingleActionProducer
    linearMultiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    -- Same-object payments between the previously separate compiler surfaces.
    -- These remain explicit because the old capstone is set/basis-level while
    -- the corrected route is linear/representation-level.
    historicalCapstoneUsesSameSelected3BAction : Set
    homSpaceUsesSameLiteralZetaSector : Set
    sourcePaidCharacterUsesSameMultiplicityCarrier : Set

open LinearShortest3BFrontierSource public

------------------------------------------------------------------------
-- 3. Correct status of the finite chart and linear theorem route.
------------------------------------------------------------------------

record CorrectedShortestFrontierBoundary : Set where
  constructor corrected-shortest-frontier-boundary
  field
    finiteBasisChartStillValid : Bool
    finiteAppraisalSlicesStillValidAfterRecognition : Bool
    pureFinNinetyInertiaRouteRefuted : Bool
    scalarMonomialRouteAutomaticallyExcluded : Bool
    actualLinearSameActionStillRequired : Bool
    linearHomEvaluationStillRequired : Bool
    actualInverseCocycleLiftStillRequired : Bool
    twelveSeventyEightCharacterAlreadyPaid : Bool
    genericCharacterMultiplicitySourceWritten : Bool
    genericIsotypicCompilerStillNeedsKernelReceipt : Bool
    actualTwelveSeventyEightLinearIntertwinerPaid : Bool
open CorrectedShortestFrontierBoundary public

canonicalCorrectedShortestFrontierBoundary : CorrectedShortestFrontierBoundary
canonicalCorrectedShortestFrontierBoundary = corrected-shortest-frontier-boundary
  true true
  true false
  true true true
  true true true
  false

------------------------------------------------------------------------
-- 4. Explicit non-promotion firewalls.
------------------------------------------------------------------------

data FiniteChartCreatesLinearMultiplicityAction : Set where
data NinetySlicesCreatePermutationRepresentation : Set where
data CharacterCreatesHomEvaluation : Set where
data NonPermutationNoGoCreatesLinearAction : Set where
data QidCreatesSameAction : Set where
data DeweyCreatesSameAction : Set where
data OeisCreatesSameAction : Set where

finiteChartDoesNotCreateLinearMultiplicityAction :
  FiniteChartCreatesLinearMultiplicityAction → ⊥
finiteChartDoesNotCreateLinearMultiplicityAction ()

ninetySlicesDoNotCreatePermutationRepresentation :
  NinetySlicesCreatePermutationRepresentation → ⊥
ninetySlicesDoNotCreatePermutationRepresentation ()

characterDoesNotCreateHomEvaluation : CharacterCreatesHomEvaluation → ⊥
characterDoesNotCreateHomEvaluation ()

noGoDoesNotCreateLinearAction : NonPermutationNoGoCreatesLinearAction → ⊥
noGoDoesNotCreateLinearAction ()

qidDoesNotCreateSameAction : QidCreatesSameAction → ⊥
qidDoesNotCreateSameAction ()

deweyDoesNotCreateSameAction : DeweyCreatesSameAction → ⊥
deweyDoesNotCreateSameAction ()

oeisDoesNotCreateSameAction : OeisCreatesSameAction → ⊥
oeisDoesNotCreateSameAction ()

------------------------------------------------------------------------
-- 5. Identifier/classification coordinates stay descriptive only.
------------------------------------------------------------------------

record CorrectedFrontierExternalCoordinates : Set where
  constructor corrected-frontier-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasSameActionAuthority : Bool
open CorrectedFrontierExternalCoordinates public

canonicalCorrectedFrontierExternalCoordinates : CorrectedFrontierExternalCoordinates
canonicalCorrectedFrontierExternalCoordinates = corrected-frontier-external-coordinates
  "Q1055807"
  "Q600043"
  "Q1057968"
  "512.22"
  "512.23"
  "A005052 remains numeric provenance for 90=10*3^2 only; it has no authority for linear actions, Hom spaces or intertwiners"
  false

------------------------------------------------------------------------
-- 6. Imported frontier snapshots: these are archaeology/status references,
--    not proof promotion by import.
------------------------------------------------------------------------

historicalFiniteBasisBoundary : Historical.Shortest3BFrontierBoundary
historicalFiniteBasisBoundary = Historical.canonicalShortest3BFrontierBoundary

linearZetaFrontier : LinearZeta.LinearZetaSectorFrontier
linearZetaFrontier = LinearZeta.currentLinearZetaSectorFrontier

linearHomFrontier : Hom.LinearMultiplicityHomFrontier
linearHomFrontier = Hom.currentLinearMultiplicityHomFrontier

permutationNoGoFrontier : NoGo.SuzukiNinetyPermutationNoGoFrontier
permutationNoGoFrontier = NoGo.currentSuzukiNinetyPermutationNoGoFrontier

characterFrontier : Character.PhaseCharacterWeldFrontier
characterFrontier = Character.currentPhaseCharacterWeldFrontier

isotypicCompilerFrontier : Isotypic.TwoIsotypicCompilerFrontier
isotypicCompilerFrontier = Isotypic.currentTwoIsotypicCompilerFrontier
