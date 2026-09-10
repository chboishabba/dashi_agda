module DASHI.Wikimedia.IbrahimPointedCompletion369MonsterJSourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Pointed
import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as Two
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine
import DASHI.Wikimedia.IbrahimC3ZetaRegularCharacterOEISQuantumGRBidiExact as Zeta
import DASHI.Wikimedia.JInvariantOEISExactPrefixSameObjectSnowballExact as JPrefix

------------------------------------------------------------------------
-- POINTED COMPLETION SNOWBALL
--
-- The repo already owns the generic construction shape
--
--   PointedExtension A role = A + UnitAt role
--
-- with role-indexed units and exact carrier isomorphisms for several Base369 /
-- Monster completions.  This file collates those completions with the 3B/OEIS
-- and J coefficient lanes.  Shared X -> X+1 shape is retained; unit identity
-- is deliberately not promoted across roles.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact completion family.
------------------------------------------------------------------------

eightPlusOneIsNine : 8 + 1 ≡ 9
eightPlusOneIsNine = refl

ninePlusOneIsTen : 9 + 1 ≡ 10
ninePlusOneIsTen = refl

fiftyThreePlusOneIsFiftyFour : 53 + 1 ≡ 54
fiftyThreePlusOneIsFiftyFour = refl

monsterPlusOneIsMoonshineWeightTwo : 196883 + 1 ≡ 196884
monsterPlusOneIsMoonshineWeightTwo = refl

pointedNineCarrier = Pointed.modePhase9IsReduced8PlusIdentity
pointedTenCarrier = Pointed.pointed10IsModePhase9PlusCompletionJ
pointedFiftyFourCarrier = Pointed.modeBoundary54Is53PlusInvariant

------------------------------------------------------------------------
-- Unit contributions are not equal merely because every completion adds one
-- point at the carrier-cardinality level.
------------------------------------------------------------------------

coarseJUnitContribution : Nat
coarseJUnitContribution = Two.unitContribution Two.coarseJCompletionUnit

localBoundaryUnitContribution : Nat
localBoundaryUnitContribution = Two.unitContribution Two.secondaryInvariantUnit

weightTwoUnitContribution : Nat
weightTwoUnitContribution = Two.unitContribution Two.weightTwoConformalUnit

coarseJUnitContributesFineFibre : coarseJUnitContribution ≡ 19683
coarseJUnitContributesFineFibre = Two.coarseJUnitContributesFullFineFibre

localBoundaryUnitContributesOne : localBoundaryUnitContribution ≡ 1
localBoundaryUnitContributesOne = Two.secondaryUnitContributesOneDimension

weightTwoUnitContributesOne : weightTwoUnitContribution ≡ 1
weightTwoUnitContributesOne = Two.conformalUnitContributesOneDimension

------------------------------------------------------------------------
-- Interaction with the 1+2+6 bulk stratification.
------------------------------------------------------------------------

bulk196830FromOneTwoSix : 196830 ≡ 3 * 90 * 729
bulk196830FromOneTwoSix = Nine.regularBulkAsThreeTimesNinetyTimes729

monsterAsPointedBulkResidual : 196883 ≡ 196830 + 53
monsterAsPointedBulkResidual = refl

weightTwoAsPointedBulkFullBoundary : 196884 ≡ 196830 + 54
weightTwoAsPointedBulkFullBoundary = refl

jCoefficientAtOneIs196884 : JPrefix.repoJ JPrefix.one ≡ 196884
jCoefficientAtOneIs196884 = JPrefix.repoJMatchesA000521Prefix JPrefix.one

zetaRegularCancellation = Zeta.regularC3CancellationAt65610

------------------------------------------------------------------------
-- External identity / sequence coordinates.
------------------------------------------------------------------------

record PointedCompletionExternalCoordinates : Set where
  constructor pointed-completion-external-coordinates
  field
    setQid : String
    cyclicGroupQid : String
    regularRepresentationQid : String
    jInvariantQid : String
    monstrousMoonshineQid : String
    powersOfThreeOEIS : String
    tenTimesPowersOfThreeOEIS : String
    jCoefficientOEIS : String
    monsterRepresentationDegreeOEIS : String
    externalIdsCreateUnitRoleIdentity : Bool
open PointedCompletionExternalCoordinates public

canonicalPointedCompletionExternalCoordinates : PointedCompletionExternalCoordinates
canonicalPointedCompletionExternalCoordinates = pointed-completion-external-coordinates
  "Q36161" "Q245462" "Q1555242" "Q287419" "Q392440"
  "A000244" "A005052" "A000521" "A001379"
  false

------------------------------------------------------------------------
-- Primary-source roles.
------------------------------------------------------------------------

griessSource : Attribution.AttributedSource
griessSource = Attribution.mkDOISource
  "Robert L. Griess Jr."
  "The Friendly Giant"
  "Inventiones Mathematicae 69, 1-102"
  "1982"
  "10.1007/BF01389186"
  "https://doi.org/10.1007/BF01389186"
  Attribution.academicArticleSource
  "primary Monster/Griess-algebra provenance for the 196883-dimensional nontrivial component and 196884-dimensional weight-two setting; not a source for Base369 pointed-completion semantics"
  Attribution.publicAttribution

conwayNortonSource : Attribution.AttributedSource
conwayNortonSource = Attribution.mkDOISource
  "John H. Conway; Simon P. Norton"
  "Monstrous Moonshine"
  "Bulletin of the London Mathematical Society 11, 308-339"
  "1979"
  "10.1112/blms/11.3.308"
  "https://doi.org/10.1112/blms/11.3.308"
  Attribution.academicArticleSource
  "primary moonshine provenance for the Monster/modular-function coefficient relationship; not a source for the internal Base369 unit-role construction"
  Attribution.publicAttribution

griessAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt griessSource
conwayNortonAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt conwayNortonSource

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

data SameCardinalityCompletionCreatesSameUnit : Set where
data JCoefficientCreatesPointedCarrier : Set where
data PointedCarrierCreatesMonsterAction : Set where
data SameOnePlusShapeCreatesSameSourceRole : Set where

sameCompletionShapeDoesNotIdentifyUnit : SameCardinalityCompletionCreatesSameUnit → ⊥
sameCompletionShapeDoesNotIdentifyUnit ()

jCoefficientDoesNotCreatePointedCarrier : JCoefficientCreatesPointedCarrier → ⊥
jCoefficientDoesNotCreatePointedCarrier ()

pointedCarrierDoesNotCreateMonsterAction : PointedCarrierCreatesMonsterAction → ⊥
pointedCarrierDoesNotCreateMonsterAction ()

sameShapeDoesNotIdentifySourceRole : SameOnePlusShapeCreatesSameSourceRole → ⊥
sameShapeDoesNotIdentifySourceRole ()

record PointedCompletionFrontier : Set where
  constructor pointed-completion-frontier
  field
    eightToNinePointedCarrierPaid : Bool
    nineToTenPointedCarrierPaid : Bool
    fiftyThreeToFiftyFourPointedCarrierPaid : Bool
    oneNineSixEightThreeToOneNineSixEightFourArithmeticPaid : Bool
    coarseJUnitFineFibreContributionPaid : Bool
    secondaryInvariantSingleUnitContributionPaid : Bool
    conformalSingleUnitContributionPaid : Bool
    oneTwoSixBulk196830Paid : Bool
    jQ1Coefficient196884Paid : Bool
    sharedPointedShapeIdentifiesUnitRoles : Bool
    semanticMonsterConstituentBridgePaidUpstream : Bool
    nextResidual : String
open PointedCompletionFrontier public

currentPointedCompletionFrontier : PointedCompletionFrontier
currentPointedCompletionFrontier = pointed-completion-frontier
  true true true true true true true true true false false
  "construct the existing MonsterConstituentSemanticBridge / same-action representation bridge; then test which role-indexed pointed completions admit structure-preserving intertwiners, rather than identifying the quotient identity, j completion, 54-invariant line and conformal line from their common +1 cardinality shape"
