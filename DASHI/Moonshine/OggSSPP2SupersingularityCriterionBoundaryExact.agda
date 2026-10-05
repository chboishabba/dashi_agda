module DASHI.Moonshine.OggSSPP2SupersingularityCriterionBoundaryExact where

------------------------------------------------------------------------
-- p=2 SUPERSINGULARITY CRITERION AUTHORITY BOUNDARY
--
-- EXTERNAL SOURCE
--
-- John Voight, Quaternion Algebras, GTM 288, Springer (2021),
-- Proposition 42.1.7, citing Silverman, Arithmetic of Elliptic Curves V.3.1:
--
--   E supersingular  <->  E[p](k^alg) = {0}.
--
-- DASHI DISCIPLINE
--
-- Agda currently does not own the explicit characteristic-two elliptic-curve
-- carrier needed to instantiate this criterion.  Therefore the source theorem
-- is represented as a semantic authority contract rather than by defining
-- "supersingular" to mean geometric p-torsion triviality.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record P2GeometricCurveProperty : Set₁ where
  field
    CurveState : Set
    geometricTwoTorsionTrivial : Set

open P2GeometricCurveProperty public

record SourceSupersingularityMeaning : Set₁ where
  field
    supersingular : Set

open SourceSupersingularityMeaning public

record SupersingularityCriterionAuthority
  (candidate : P2GeometricCurveProperty)
  (meaning : SourceSupersingularityMeaning) : Set₁ where
  field
    criterionForward :
      supersingular meaning ->
      geometricTwoTorsionTrivial candidate

    criterionReverse :
      geometricTwoTorsionTrivial candidate ->
      supersingular meaning

    sourceTitle : String
    sourceLocator : String

open SupersingularityCriterionAuthority public

candidateSupersingularFromCriterion :
  {candidate : P2GeometricCurveProperty} ->
  {meaning : SourceSupersingularityMeaning} ->
  SupersingularityCriterionAuthority candidate meaning ->
  geometricTwoTorsionTrivial candidate ->
  supersingular meaning
candidateSupersingularFromCriterion authority =
  criterionReverse authority

data CriterionCitationCreatesCurveCarrier : Set where
data CriterionCitationCreatesSupersingularityProof : Set where

criterionCitationDoesNotCreateCurveCarrier :
  CriterionCitationCreatesCurveCarrier -> ⊥
criterionCitationDoesNotCreateCurveCarrier ()

criterionCitationDoesNotCreateSupersingularityProof :
  CriterionCitationCreatesSupersingularityProof -> ⊥
criterionCitationDoesNotCreateSupersingularityProof ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

sourceReference : String
sourceReference =
  "John Voight, Quaternion Algebras, GTM 288, Springer (2021), Proposition 42.1.7; citing Silverman V.3.1"

record SupersingularityCriterionBoundary : Set where
  constructor supersingularity-criterion-boundary
  field
    sourceCriterionRecorded : Bool
    criterionKeptSeparateFromDefinition : Bool
    explicitAgdaP2CurveCarrierOwned : Bool
    geometricTwoTorsionTheoremOwnedInAgda : Bool
    sourceCriterionAuthorityInhabitedInAgda : Bool
    p2SupersingularityRecognizedInAgda : Bool

canonicalSupersingularityCriterionBoundary :
  SupersingularityCriterionBoundary
canonicalSupersingularityCriterionBoundary =
  supersingularity-criterion-boundary
    true true false false false false
