module DASHI.Moonshine.Monster3BActualMultiplicityIntertwinerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- State the actual promotion layer in map-level form.  The multiplicity space
-- is not identified by dimension alone: an evaluation map, a constructive
-- inverse, and E-equivariance are required.  From those data this module proves
-- injectivity and surjectivity rather than accepting them as separate receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record ActualMultiplicityEvaluationData : Set₁ where
  field
    ExtraspecialElement : Set
    HeisenbergCarrier : Set
    MultiplicityCarrier : Set
    TensorCarrier : Set
    ActualZetaSector : Set

    actHeisenberg :
      ExtraspecialElement → HeisenbergCarrier → HeisenbergCarrier
    actTensor :
      ExtraspecialElement → TensorCarrier → TensorCarrier
    actActualSector :
      ExtraspecialElement → ActualZetaSector → ActualZetaSector

    pureTensor :
      HeisenbergCarrier → MultiplicityCarrier → TensorCarrier

    evaluationMap : TensorCarrier → ActualZetaSector
    evaluationInverse : ActualZetaSector → TensorCarrier

    inverseAfterEvaluation :
      (value : TensorCarrier) →
      evaluationInverse (evaluationMap value) ≡ value

    evaluationAfterInverse :
      (value : ActualZetaSector) →
      evaluationMap (evaluationInverse value) ≡ value

    evaluationEEquivariant :
      (e : ExtraspecialElement) →
      (value : TensorCarrier) →
      evaluationMap (actTensor e value)
      ≡ actActualSector e (evaluationMap value)

open ActualMultiplicityEvaluationData public

actualEvaluationMapInjective :
  (data : ActualMultiplicityEvaluationData) →
  {left right : TensorCarrier data} →
  evaluationMap data left ≡ evaluationMap data right →
  left ≡ right
actualEvaluationMapInjective data {left} {right} equality =
  trans
    (sym (inverseAfterEvaluation data left))
    (trans
      (cong (evaluationInverse data) equality)
      (inverseAfterEvaluation data right))

actualEvaluationMapSurjective :
  (data : ActualMultiplicityEvaluationData) →
  (value : ActualZetaSector data) →
  Σ (TensorCarrier data)
    (λ preimage → evaluationMap data preimage ≡ value)
actualEvaluationMapSurjective data value =
  evaluationInverse data value , evaluationAfterInverse data value

record ActualEvaluationIsomorphism : Set₁ where
  field
    Domain : Set
    Codomain : Set
    forward : Domain → Codomain
    inverse : Codomain → Domain
    leftInverse : (value : Domain) → inverse (forward value) ≡ value
    rightInverse : (value : Codomain) → forward (inverse value) ≡ value

open ActualEvaluationIsomorphism public

actualEvaluationIntertwiner :
  (data : ActualMultiplicityEvaluationData) →
  ActualEvaluationIsomorphism
actualEvaluationIntertwiner data = record
  { Domain = TensorCarrier data
  ; Codomain = ActualZetaSector data
  ; forward = evaluationMap data
  ; inverse = evaluationInverse data
  ; leftInverse = inverseAfterEvaluation data
  ; rightInverse = evaluationAfterInverse data
  }

record ActualEvaluationEquivariantIsomorphism
  (data : ActualMultiplicityEvaluationData) : Set₁ where
  field
    isomorphism : ActualEvaluationIsomorphism
    intertwinesE :
      (e : ExtraspecialElement data) →
      (value : TensorCarrier data) →
      forward isomorphism (actTensor data e value)
      ≡ actActualSector data e (forward isomorphism value)

open ActualEvaluationEquivariantIsomorphism public

actualMonsterLocalModuleIntertwiner :
  (data : ActualMultiplicityEvaluationData) →
  ActualEvaluationEquivariantIsomorphism data
actualMonsterLocalModuleIntertwiner data = record
  { isomorphism = actualEvaluationIntertwiner data
  ; intertwinesE = evaluationEEquivariant data
  }
