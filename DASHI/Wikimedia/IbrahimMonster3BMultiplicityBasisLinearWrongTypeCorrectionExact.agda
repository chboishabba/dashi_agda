module DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (_∷_; [])

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Interop.SensibLawOntologyTopology as WrongType
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Basis
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as OldAction
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as CharacterWeld
import DASHI.Wikimedia.IbrahimMonsterCharacterToTwoIsotypicBlocksMathlibSnowballExact as Isotypic

------------------------------------------------------------------------
-- MULTIPLICITY BASIS INDEX != LINEAR MULTIPLICITY REPRESENTATION
--
-- The existing model has a perfectly valid finite BASIS/COPY index:
--
--     ModelMultiplicitySpace = Fin 90
--     ModelTensorBasis       = X6 x Fin 90.
--
-- This is enough for the finite Schrödinger-basis model and for Heisenberg
-- translations, which act on X6 and leave the copy index fixed.
--
-- A later owner strengthened this to
--
--     multiplicityAct : Inertia -> Fin 90 -> Fin 90.
--
-- That is a genuine PERMUTATION-BASIS hypothesis: it says the whole inertia
-- action permutes the ninety chosen multiplicity basis labels.
--
-- Barraclough--Wilson / character theory instead pays a 90-DIMENSIONAL LINEAR
-- multiplicity representation with character 12 + 78.  A general linear
-- representation need not preserve a chosen basis.  Therefore:
--
--     90 basis labels
--       !=
--     a 90-dimensional vector space,
--
-- and
--
--     character 12+78
--       !=
--     an action Fin 90 -> Fin 90.
--
-- The old Fin90 action interface remains useful as an OPTIONAL monomial /
-- permutation-basis route, but it is not a mandatory consequence of the
-- Monster character calculation.  The canonical mandatory object is an actual
-- linear multiplicity representation S_zeta; only a separate basis-preserving
-- receipt may specialize it to a Fin90 permutation action.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution: representation theory source is kept separate from the
--    repository's finite-basis model.
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
  "primary source for the 729-times-(12 plus 78) multiplicity CHARACTER/linear-representation structure; it does not assert a ninety-point permutation basis"
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
  "representation-theory calibration for the distinction between a vector-space representation and a permutation representation on a chosen basis"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 2. Two distinct carriers.
------------------------------------------------------------------------

MultiplicityBasisIndex : Set
MultiplicityBasisIndex = Fin 90

basisIndexCount : Nat
basisIndexCount = 90

record LinearMultiplicityRepresentation : Set₁ where
  field
    Scalar : Set
    Vector : Set
    Inertia : Set

    zeroVector : Vector
    addVector : Vector → Vector → Vector
    scaleVector : Scalar → Vector → Vector
    inertiaAct : Inertia → Vector → Vector

    -- These are intentionally proof-bearing obligations rather than assumed
    -- from the existence of a 90-element basis index.
    actionPreservesZero : Set
    actionPreservesAddition : Set
    actionPreservesScaling : Set
    vectorDimensionIsNinety : Set

open LinearMultiplicityRepresentation public

record PermutationBasisSpecialisation
    (linear : LinearMultiplicityRepresentation) : Set₁ where
  field
    basisVector : MultiplicityBasisIndex → Vector linear
    basisIsComplete : Set
    basisIsIndependent : Set

    basisPermutation : Inertia linear → MultiplicityBasisIndex → MultiplicityBasisIndex

    actionPreservesChosenBasis :
      (g : Inertia linear) →
      (i : MultiplicityBasisIndex) →
      inertiaAct linear g (basisVector i)
      ≡ basisVector (basisPermutation g i)

open PermutationBasisSpecialisation public

------------------------------------------------------------------------
-- 3. Existing model ownership remains valid at basis-index level.
------------------------------------------------------------------------

existingBasisIndexIsFin90 : Basis.ModelMultiplicitySpace ≡ Fin 90
existingBasisIndexIsFin90 = refl

record ExistingFinNinetyRouteClassification : Set where
  constructor existing-fin-ninety-route-classification
  field
    basisIndexCarrierOwned : Bool
    tensorBasisCarrierOwned : Bool
    heisenbergTranslationLeavesMultiplicityIndexFixed : Bool
    fullInertiaPermutationBasisPaid : Bool
    fullInertiaPermutationBasisIsMandatory : Bool
open ExistingFinNinetyRouteClassification public

canonicalExistingFinNinetyRouteClassification : ExistingFinNinetyRouteClassification
canonicalExistingFinNinetyRouteClassification =
  existing-fin-ninety-route-classification
    true true true
    false
    false

------------------------------------------------------------------------
-- 4. WrongType classification using the existing repo ontology shell.
------------------------------------------------------------------------

basisVsLinearWrongTypeId : WrongType.StableId
basisVsLinearWrongTypeId = WrongType.stableId "wrongtype:monster3b:fin90-basis-index-vs-linear-multiplicity"

representationSystemId : WrongType.StableId
representationSystemId = WrongType.stableId "system:finite-group-linear-representation"

characterSourceId : WrongType.StableId
characterSourceId = WrongType.stableId "source:doi:10.1112/S1461157000001352"

basisVsLinearWrongType : WrongType.WrongType
basisVsLinearWrongType = WrongType.wrongTypeRecord
  basisVsLinearWrongTypeId
  representationSystemId
  (characterSourceId ∷ [])
  [] [] []
  WrongType.strict
  [] [] []

------------------------------------------------------------------------
-- 5. Explicit non-promotion firewalls.
------------------------------------------------------------------------

data NinetyBasisLabelsCreateNinetyDimensionalVectorSpace : Set where
data NinetyDimensionalVectorSpaceCreatesFinNinetyPermutationAction : Set where
data CharacterTwelvePlusSeventyEightCreatesBasisPermutation : Set where
data HeisenbergTranslationBasisPermutationCreatesInertiaBasisPermutation : Set where
data SetBijectionCreatesLinearIsomorphism : Set where
data DegreeOccurrenceCreatesLinearAction : Set where
data OeisCreatesPermutationBasis : Set where

basisLabelsDoNotCreateVectorSpace : NinetyBasisLabelsCreateNinetyDimensionalVectorSpace → ⊥
basisLabelsDoNotCreateVectorSpace ()

vectorSpaceDoesNotCreatePermutationAction :
  NinetyDimensionalVectorSpaceCreatesFinNinetyPermutationAction → ⊥
vectorSpaceDoesNotCreatePermutationAction ()

characterDoesNotCreateBasisPermutation :
  CharacterTwelvePlusSeventyEightCreatesBasisPermutation → ⊥
characterDoesNotCreateBasisPermutation ()

heisenbergBasisPermutationDoesNotCreateInertiaBasisPermutation :
  HeisenbergTranslationBasisPermutationCreatesInertiaBasisPermutation → ⊥
heisenbergBasisPermutationDoesNotCreateInertiaBasisPermutation ()

setBijectionDoesNotCreateLinearIso : SetBijectionCreatesLinearIsomorphism → ⊥
setBijectionDoesNotCreateLinearIso ()

degreeOccurrenceDoesNotCreateLinearAction : DegreeOccurrenceCreatesLinearAction → ⊥
degreeOccurrenceDoesNotCreateLinearAction ()

oeisDoesNotCreatePermutationBasis : OeisCreatesPermutationBasis → ⊥
oeisDoesNotCreatePermutationBasis ()

------------------------------------------------------------------------
-- 6. Source/QID/Dewey/OEIS coordinates remain non-promoting.
------------------------------------------------------------------------

record LinearMultiplicityExternalCoordinates : Set where
  constructor linear-multiplicity-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasCarrierAuthority : Bool
open LinearMultiplicityExternalCoordinates public

canonicalLinearMultiplicityExternalCoordinates : LinearMultiplicityExternalCoordinates
canonicalLinearMultiplicityExternalCoordinates = linear-multiplicity-external-coordinates
  "Q1055807"
  "Q600043"
  "Q1057968"
  "512.22"
  "512.23"
  "A005052 is numerical provenance for 90 = 10*3^2 only; it does not identify a vector space, basis, matrix action or permutation representation"
  false

------------------------------------------------------------------------
-- 7. Corrected proof frontier.
------------------------------------------------------------------------

record MultiplicityWrongTypeFrontier : Set where
  constructor multiplicity-wrongtype-frontier
  field
    finNinetyBasisIndexOwned : Bool
    finiteTensorBasisOwned : Bool
    heisenbergBasisPermutationOwned : Bool
    sourcePaidLinearCharacterTwelvePlusSeventyEight : Bool
    phaseResolvedCharacterFamilyPaid : Bool
    finNinetyPermutationInertiaActionPaid : Bool
    finNinetyPermutationInertiaActionMandatory : Bool
    actualLinearMultiplicityRepresentationPaid : Bool
    linearTwelveSeventyEightDecompositionPaid : Bool
    chosenBasisPreservedByFullInertiaPaid : Bool
    oldFinNinetyAttachmentUsableConditionally : Bool
    nextResidual : String
open MultiplicityWrongTypeFrontier public

currentMultiplicityWrongTypeFrontier : MultiplicityWrongTypeFrontier
currentMultiplicityWrongTypeFrontier = multiplicity-wrongtype-frontier
  true true true true true
  false false
  false false false
  true
  "repair the Monster promotion route at the linear-representation level. The mandatory target is an actual 90-dimensional multiplicity representation S_zeta carrying the source-paid character chi_12 + chi_78, together with a same-object linear evaluation/intertwiner W_zeta ≃ H_zeta tensor S_zeta. The generic mathlib isotypic compiler can then split S_zeta into the 12 and 78 invariant blocks. The historical Fin90 basis-index action remains available only as an optional specialisation after a separate proof that the full inertia action preserves/permutates the chosen ninety basis vectors. Do not use 90 basis labels, set-level recognition, Heisenberg translation equivariance, degree occurrence, QID/Dewey/OEIS, or character equality to manufacture that permutation-basis theorem."

characterFrontier : CharacterWeld.PhaseCharacterWeldFrontier
characterFrontier = CharacterWeld.currentPhaseCharacterWeldFrontier

isotypicFrontier : Isotypic.TwoIsotypicCompilerFrontier
isotypicFrontier = Isotypic.currentTwoIsotypicCompilerFrontier

oldFinNinetyBoundary : OldAction.MultiplicityInertiaTwelveSeventyEightBoundary
oldFinNinetyBoundary = OldAction.canonicalMultiplicityInertiaTwelveSeventyEightBoundary
