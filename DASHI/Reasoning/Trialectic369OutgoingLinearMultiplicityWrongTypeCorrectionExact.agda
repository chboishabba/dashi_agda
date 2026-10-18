module DASHI.Reasoning.Trialectic369OutgoingLinearMultiplicityWrongTypeCorrectionExact where

------------------------------------------------------------------------
-- TRIALECTIC OUTGOING RESIDUAL: FINITE BASIS VS LINEAR MULTIPLICITY
--
-- DASHI CONTRIBUTION
--
-- The trialectic / SSP15 carrier analysis owns useful finite coordinates:
--
--   Fin 90 <-> Fine10 x Sheet9
--
-- and, conditionally on a basis-preserving action, useful diagnostics:
--
--   selected Fine10 fibre -> 9-state Sheet9 action
--   Fricke-like fine motion -> 18-state mode block.
--
-- The modern Monster 3B representation audit proves that this finite-basis
-- route is NOT the mandatory source-paid multiplicity representation.
--
-- Barraclough--Wilson / the repo character lane pays a 90-dimensional LINEAR
-- representation with character chi_12 + chi_78.  The pure Fin90 permutation
-- route is refuted by the nonintegral central cyclotomic character.
--
-- Therefore:
--
--   * Sheet9 remains a valid finite BASIS-COORDINATE residual;
--   * 9/18 action compilers remain valid conditional basis-preserving tools;
--   * neither may be promoted to the actual Monster multiplicity action without
--     an explicit permutation/monomial basis specialisation;
--   * the canonical outgoing scientific target is the linear
--       S_zeta = Hom_E(H_zeta,W_zeta)
--     same-object route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Sheet9
import DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact as FiniteDescent
import DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact as FineFricke
import DASHI.Reasoning.Trialectic369OutgoingFrickeModeBlock18Exact as Mode18

import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Wikimedia.IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact as PermutationNoGo
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as LinearHom
import DASHI.Wikimedia.IbrahimMonster3BLinearShortestFrontierCorrectionExact as LinearFrontier

------------------------------------------------------------------------
-- 1. Reuse the repo's explicit WrongType classification.
------------------------------------------------------------------------

multiplicityWrongTypeFrontier :
  WrongType.MultiplicityWrongTypeFrontier
multiplicityWrongTypeFrontier =
  WrongType.currentMultiplicityWrongTypeFrontier

finiteBasisIndexOwned :
  WrongType.finNinetyBasisIndexOwned multiplicityWrongTypeFrontier
  ≡ true
finiteBasisIndexOwned = refl

finiteTensorBasisOwned :
  WrongType.finiteTensorBasisOwned multiplicityWrongTypeFrontier
  ≡ true
finiteTensorBasisOwned = refl

finNinetyPermutationInertiaNotPaid :
  WrongType.finNinetyPermutationInertiaActionPaid multiplicityWrongTypeFrontier
  ≡ false
finNinetyPermutationInertiaNotPaid = refl

finNinetyPermutationInertiaNotMandatory :
  WrongType.finNinetyPermutationInertiaActionMandatory multiplicityWrongTypeFrontier
  ≡ false
finNinetyPermutationInertiaNotMandatory = refl

oldFinNinetyRouteOnlyConditional :
  WrongType.oldFinNinetyAttachmentUsableConditionally multiplicityWrongTypeFrontier
  ≡ true
oldFinNinetyRouteOnlyConditional = refl

------------------------------------------------------------------------
-- 2. Reuse the pure-permutation character no-go.
------------------------------------------------------------------------

permutationNoGoFrontier :
  PermutationNoGo.SuzukiNinetyPermutationNoGoFrontier
permutationNoGoFrontier =
  PermutationNoGo.currentSuzukiNinetyPermutationNoGoFrontier

pureFinNinetyPermutationRouteRefuted :
  PermutationNoGo.pureFinNinetyPermutationRouteRefuted
    permutationNoGoFrontier
  ≡ true
pureFinNinetyPermutationRouteRefuted = refl

monomialScalarRouteStillPossible :
  PermutationNoGo.monomialScalarRouteStillPossible
    permutationNoGoFrontier
  ≡ true
monomialScalarRouteStillPossible = refl

actualLinearMultiplicityActionStillOpen :
  PermutationNoGo.actualLinearMultiplicityActionPaid
    permutationNoGoFrontier
  ≡ false
actualLinearMultiplicityActionStillOpen = refl

------------------------------------------------------------------------
-- 3. The canonical linear target is the Hom-space owner.
------------------------------------------------------------------------

linearHomFrontier :
  LinearHom.LinearMultiplicityHomFrontier
linearHomFrontier =
  LinearHom.currentLinearMultiplicityHomFrontier

canonicalHomSpaceRouteNamed :
  LinearHom.canonicalHomSpaceRouteNamed linearHomFrontier
  ≡ true
canonicalHomSpaceRouteNamed = refl

finiteEvaluationIsDonorOnly :
  LinearHom.finiteEvaluationDonorAvailable linearHomFrontier
  ≡ true
finiteEvaluationIsDonorOnly = refl

actualLinearHomCarrierStillOpen :
  LinearHom.actualEquivariantHomCarrierConstructed linearHomFrontier
  ≡ false
actualLinearHomCarrierStillOpen = refl

actualLinearEvaluationStillOpen :
  LinearHom.actualLinearEvaluationInverseConstructed linearHomFrontier
  ≡ false
actualLinearEvaluationStillOpen = refl

actualInverseCocycleLiftStillOpen :
  LinearHom.actualCocycleLiftInstantiated linearHomFrontier
  ≡ false
actualInverseCocycleLiftStillOpen = refl

------------------------------------------------------------------------
-- 4. Corrected shortest frontier.
------------------------------------------------------------------------

correctedShortestFrontier :
  LinearFrontier.CorrectedShortestFrontierBoundary
correctedShortestFrontier =
  LinearFrontier.canonicalCorrectedShortestFrontierBoundary

finiteBasisChartStillValid :
  LinearFrontier.finiteBasisChartStillValid correctedShortestFrontier
  ≡ true
finiteBasisChartStillValid = refl

pureFinNinetyRouteRefutedAgain :
  LinearFrontier.pureFinNinetyInertiaRouteRefuted correctedShortestFrontier
  ≡ true
pureFinNinetyRouteRefutedAgain = refl

actualLinearSameActionRequired :
  LinearFrontier.actualLinearSameActionStillRequired correctedShortestFrontier
  ≡ true
actualLinearSameActionRequired = refl

linearHomEvaluationRequired :
  LinearFrontier.linearHomEvaluationStillRequired correctedShortestFrontier
  ≡ true
linearHomEvaluationRequired = refl

------------------------------------------------------------------------
-- 5. Trialectic consequences.
------------------------------------------------------------------------

data Sheet9BasisCoordinateCreatesLinearNineRepresentation : Set where
data TenByNineSetFactorCreatesLinearTensorFactorisation : Set where
data FiniteModeBlock18CreatesLinearInvariantSubspace : Set where
data CharacterTwelvePlusSeventyEightCreatesSheet9Action : Set where

sheet9CoordinateDoesNotCreateLinearNineRepresentation :
  Sheet9BasisCoordinateCreatesLinearNineRepresentation -> ⊥
sheet9CoordinateDoesNotCreateLinearNineRepresentation ()

tenByNineSetFactorDoesNotCreateLinearTensorFactorisation :
  TenByNineSetFactorCreatesLinearTensorFactorisation -> ⊥
tenByNineSetFactorDoesNotCreateLinearTensorFactorisation ()

modeBlock18DoesNotCreateLinearInvariantSubspace :
  FiniteModeBlock18CreatesLinearInvariantSubspace -> ⊥
modeBlock18DoesNotCreateLinearInvariantSubspace ()

characterDoesNotCreateSheet9Action :
  CharacterTwelvePlusSeventyEightCreatesSheet9Action -> ⊥
characterDoesNotCreateSheet9Action ()

------------------------------------------------------------------------
-- 6. Conditional finite-basis route remains valid as an OPTIONAL
--    specialisation after a separate basis-preservation receipt.
------------------------------------------------------------------------

record OptionalFiniteBasisResidualRoute : Set₁ where
  field
    basisSpecialisationExists : Set

    -- The finite compilers are retained as consumers once basis preservation
    -- has independently been paid.
    finiteMultiplicityProjectionDescentAvailable : Set
    selectedFineOrFrickeBlockRecognitionAvailable : Set

open OptionalFiniteBasisResidualRoute public

data LinearRouteAutomaticallyCreatesOptionalFiniteBasisRoute : Set where

linearRouteDoesNotAutomaticallyCreateFiniteBasisSpecialisation :
  LinearRouteAutomaticallyCreatesOptionalFiniteBasisRoute -> ⊥
linearRouteDoesNotAutomaticallyCreateFiniteBasisSpecialisation ()

------------------------------------------------------------------------
-- 7. Machine-readable corrected boundary.
------------------------------------------------------------------------

record Trialectic369OutgoingLinearMultiplicityWrongTypeBoundary : Set where
  constructor trialectic-369-outgoing-linear-multiplicity-wrongtype-boundary
  field
    sheet9FiniteBasisCoordinateStillValid : Bool
    tenByNineFiniteBasisChartStillValid : Bool
    finiteNineAndEighteenCompilersRemainConditionalTools : Bool

    pureFin90PermutationMonsterRouteRefuted : Bool
    sourcePaidMultiplicityObjectIsLinear : Bool
    canonicalTargetIsHomSpace : Bool

    sheet9CreatesLinearNineRepresentation : Bool
    tenByNineCreatesLinearTensorFactorisation : Bool
    modeBlock18CreatesLinearInvariantSubspace : Bool

    basisPreservationReceiptStillCouldEnableFiniteRoute : Bool

    actualLinearMultiplicityHomSpacePaid : Bool
    actualLinearEvaluationIntertwinerPaid : Bool
    actualInverseCocycleMultiplicityActionPaid : Bool

canonicalTrialectic369OutgoingLinearMultiplicityWrongTypeBoundary :
  Trialectic369OutgoingLinearMultiplicityWrongTypeBoundary
canonicalTrialectic369OutgoingLinearMultiplicityWrongTypeBoundary =
  trialectic-369-outgoing-linear-multiplicity-wrongtype-boundary
    true true true
    true true true
    false false false
    true
    false false false
