module DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite reindexing step behind nonlinear Fourier reality.  The
-- previous Round-35 modules prove both ingredients separately:
--
--   * local term reality under canonical triad conjugation;
--   * an exact permutation
--       map canonicalConjugate (outputFiber k) ↭ outputFiber (-k).
--
-- Here we prove that the literal finite Complex3 sum is permutation-invariant,
-- that conjugation commutes with that sum, and combine the two ingredients to
-- obtain the actual system theorem
--
--   projectedNonlinearity(-k)
--     = conjugate(projectedNonlinearity(k)).
--
-- No continuum estimate, ordering convention, function extensionality or
-- caller-supplied conservation/reality witness enters the sum argument beyond
-- the physical velocity reality used by the local nonlinear term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.List.Base as ListBase
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealityRound35Exact as LocalReality
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as FibrePerm
import DASHI.Physics.Closure.NSTriadKNViscousRealityRound35Exact as ViscousReality

------------------------------------------------------------------------
-- Finite Complex3 sums respect list permutation.
------------------------------------------------------------------------

sumVectorsRespPermutation :
  ∀ {r} {F : C3.RealField r}
    {xs ys : List (C3.Complex3 F)} →
  xs Perm.↭ ys → Audit.sumVectors xs ≡ Audit.sumVectors ys
sumVectorsRespPermutation Perm.refl = refl
sumVectorsRespPermutation (Perm.prep x xs↭ys) =
  cong (C3.complex3Add x) (sumVectorsRespPermutation xs↭ys)
sumVectorsRespPermutation
    (Perm.swap {xs = xs} x y xs↭ys) =
  trans
    (sym (Algebra.complex3AddAssociative x y (Audit.sumVectors xs)))
    (trans
      (cong (λ z → C3.complex3Add z (Audit.sumVectors xs))
        (Algebra.complex3AddCommutative x y))
      (trans
        (Algebra.complex3AddAssociative y x (Audit.sumVectors xs))
        (cong
          (λ z → C3.complex3Add y (C3.complex3Add x z))
          (sumVectorsRespPermutation xs↭ys))))
sumVectorsRespPermutation (Perm.trans xs↭ys ys↭zs) =
  trans
    (sumVectorsRespPermutation xs↭ys)
    (sumVectorsRespPermutation ys↭zs)

mapTriadTermsRespPermutation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    {xs ys : List Physical.PhysicalTriadIncidence} →
  xs Perm.↭ ys →
  Audit.mapTriadTerms system xs Perm.↭ Audit.mapTriadTerms system ys
mapTriadTermsRespPermutation system Perm.refl = Perm.refl
mapTriadTermsRespPermutation system (Perm.prep x permutation) =
  Perm.prep (Audit.projectedOrderedTerm system x)
    (mapTriadTermsRespPermutation system permutation)
mapTriadTermsRespPermutation system
    (Perm.swap x y permutation) =
  Perm.swap
    (Audit.projectedOrderedTerm system x)
    (Audit.projectedOrderedTerm system y)
    (mapTriadTermsRespPermutation system permutation)
mapTriadTermsRespPermutation system (Perm.trans first second) =
  Perm.trans
    (mapTriadTermsRespPermutation system first)
    (mapTriadTermsRespPermutation system second)

------------------------------------------------------------------------
-- Conjugation commutes with the literal finite Complex3 sum.
------------------------------------------------------------------------

complex3ConjugateZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complex3Conjugate (C3.complex3Zero F) ≡ C3.complex3Zero F
complex3ConjugateZero {F = F}
  rewrite C3.negateZero F = refl

sumVectorsConjugate :
  ∀ {r} {F : C3.RealField r}
    (values : List (C3.Complex3 F)) →
  Audit.sumVectors (ListBase.map C3.complex3Conjugate values)
  ≡ C3.complex3Conjugate (Audit.sumVectors values)
sumVectorsConjugate [] = sym complex3ConjugateZero
sumVectorsConjugate (value ∷ values) =
  trans
    (cong
      (C3.complex3Add (C3.complex3Conjugate value))
      (sumVectorsConjugate values))
    (sym
      (Additive.complex3ConjugateAdd value (Audit.sumVectors values)))

------------------------------------------------------------------------
-- Canonical conjugation of one incidence carries exactly the conjugate term.
------------------------------------------------------------------------

canonicalConjugateEqualsPhysicalConjugate :
  (incidence : Physical.PhysicalTriadIncidence) →
  FibrePerm.canonicalConjugate incidence ≡ Symmetry.conjugateTriad incidence
canonicalConjugateEqualsPhysicalConjugate incidence =
  FibrePerm.physicalIncidenceExtPQ
    (FibrePerm.canonicalConjugate incidence)
    (Symmetry.conjugateTriad incidence)
    refl refl

canonicalConjugateTermReality :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  (incidence : Physical.PhysicalTriadIncidence) →
  Audit.projectedOrderedTerm system
      (FibrePerm.canonicalConjugate incidence)
  ≡ C3.complex3Conjugate
      (Audit.projectedOrderedTerm system incidence)
canonicalConjugateTermReality system velocityReality incidence =
  trans
    (cong (Audit.projectedOrderedTerm system)
      (canonicalConjugateEqualsPhysicalConjugate incidence))
    (LocalReality.projectedOrderedTermConjugateTriad
      system velocityReality incidence)

sumCanonicalConjugateTermsReality :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors
    (Audit.mapTriadTerms system
      (ListBase.map FibrePerm.canonicalConjugate incidences))
  ≡ C3.complex3Conjugate
      (Audit.sumVectors (Audit.mapTriadTerms system incidences))
sumCanonicalConjugateTermsReality system velocityReality [] =
  sym complex3ConjugateZero
sumCanonicalConjugateTermsReality system velocityReality
    (incidence ∷ incidences) =
  trans
    (cong₂ C3.complex3Add
      (canonicalConjugateTermReality system velocityReality incidence)
      (sumCanonicalConjugateTermsReality
        system velocityReality incidences))
    (sym
      (Additive.complex3ConjugateAdd
        (Audit.projectedOrderedTerm system incidence)
        (Audit.sumVectors (Audit.mapTriadTerms system incidences))))

------------------------------------------------------------------------
-- The literal summed projected nonlinearity reality theorem.
------------------------------------------------------------------------

projectedNonlinearityReality :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.RealityCondition (Audit.projectedNonlinearity system)
projectedNonlinearityReality system velocityReality output =
  let
    source = Audit.concreteTriadsAt system output

    carrierPermutation :
      ListBase.map FibrePerm.canonicalConjugate source
        Perm.↭
      Audit.concreteTriadsAt system (Z3.negateMode output)
    carrierPermutation =
      FibrePerm.canonicalConjugateOutputFiberPermutation
        (Audit.cutoff system) output

    termPermutation :
      Audit.mapTriadTerms system
        (ListBase.map FibrePerm.canonicalConjugate source)
        Perm.↭
      Audit.mapTriadTerms system
        (Audit.concreteTriadsAt system (Z3.negateMode output))
    termPermutation =
      mapTriadTermsRespPermutation system carrierPermutation
  in
  trans
    (sym (sumVectorsRespPermutation termPermutation))
    (sumCanonicalConjugateTermsReality system velocityReality source)

canonicalSummedProjectedNonlinearityReality :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  ViscousReality.SummedProjectedNonlinearityReality system
canonicalSummedProjectedNonlinearityReality system velocityReality = record
  { ViscousReality.SummedProjectedNonlinearityReality.nonlinearReality =
      projectedNonlinearityReality system velocityReality
  }

summedProjectedNonlinearityRealityClosed : Bool
summedProjectedNonlinearityRealityClosed = true

summedProjectedNonlinearityRealityClosedIsTrue :
  summedProjectedNonlinearityRealityClosed ≡ true
summedProjectedNonlinearityRealityClosedIsTrue = refl
