module DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact where

------------------------------------------------------------------------
-- ROUND111 / EXTERNAL FORCING AS A SELF-ORBIT-REMOVED OUTPUT FIBRE
--
-- Round109 identifies
--
--   N_ext = N_full - N_self
--
-- on the literal physical Galerkin system.  This module removes the remaining
-- opacity in that subtraction.  When a selected ordered incidence tau and its
-- swapped placement are distinct members of the same output fibre, the exact
-- uniqueness/removal machinery from Round35 gives a residual incidence list
-- obtained by deleting precisely those two ordered placements.
--
-- The literal finite convolution then satisfies
--
--   N_full(k)
--     = N_tau + N_swap(tau) + sum(residual fibre)
--     = N_self(tau) + sum(residual fibre),
--
-- and therefore
--
--   N_ext(tau) = sum(residual fibre).
--
-- This is the carrier bridge needed before importing the older output-fibre
-- commutator/Bony machinery.  No cancellation, absolute value, shell estimate,
-- or continuum hypothesis is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Fibre
import DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact as Sum
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split

externalResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (swapMember : Symmetry.swapTriad tau ∈
    Audit.concreteTriadsAt system (Physical.k tau)) →
  Symmetry.swapTriad tau ≢ tau →
  List Physical.PhysicalTriadIncidence
externalResidualCarrier system tau tauMember swapMember swapDifferent =
  Fibre.removeAt
    (Fibre.otherMemberSurvivesRemoval
      tauMember swapMember swapDifferent)

externalCarrierPermutation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  Audit.concreteTriadsAt system (Physical.k tau)
  Perm.↭
  tau ∷ Symmetry.swapTriad tau ∷
    externalResidualCarrier system tau tauMember swapMember swapDifferent
externalCarrierPermutation system tau tauMember swapMember swapDifferent =
  let
    afterTau = Fibre.removeAt tauMember
    swapSurvives =
      Fibre.otherMemberSurvivesRemoval tauMember swapMember swapDifferent
  in
  Perm.trans
    (Fibre.removeAtPermutation tauMember)
    (Perm.prep tau (Fibre.removeAtPermutation swapSurvives))

externalCarrierTermPermutation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  Audit.mapTriadTerms system
    (Audit.concreteTriadsAt system (Physical.k tau))
  Perm.↭
  Audit.mapTriadTerms system
    (tau ∷ Symmetry.swapTriad tau ∷
      externalResidualCarrier system tau tauMember swapMember swapDifferent)
externalCarrierTermPermutation system tau tauMember swapMember swapDifferent =
  Sum.mapTriadTermsRespPermutation system
    (externalCarrierPermutation system tau tauMember swapMember swapDifferent)

externalResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (swapMember : Symmetry.swapTriad tau ∈
    Audit.concreteTriadsAt system (Physical.k tau)) →
  Symmetry.swapTriad tau ≢ tau →
  C3.Complex3 F
externalResidualVector system tau tauMember swapMember swapDifferent =
  Audit.sumVectors
    (Audit.mapTriadTerms system
      (externalResidualCarrier system tau tauMember swapMember swapDifferent))

fullOutputFibreIsTwoSelectedTermsPlusResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  Audit.projectedNonlinearity system (Physical.k tau)
  ≡
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (C3.complex3Add
      (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))
      (externalResidualVector system tau tauMember swapMember swapDifferent))
fullOutputFibreIsTwoSelectedTermsPlusResidual
    system tau tauMember swapMember swapDifferent =
  Sum.sumVectorsRespPermutation
    (externalCarrierTermPermutation
      system tau tauMember swapMember swapDifferent)

selfForcingKIsTwoSelectedOrderedTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Split.selfForcingK system tau
  ≡
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))
selfForcingKIsTwoSelectedOrderedTerms system tau = refl

fullForcingKIsSelfPlusResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  Split.fullForcingK system tau
  ≡ C3.complex3Add
      (Split.selfForcingK system tau)
      (externalResidualVector system tau tauMember swapMember swapDifferent)
fullForcingKIsSelfPlusResidualCarrier
    system tau tauMember swapMember swapDifferent =
  let
    first = Audit.projectedOrderedTerm system tau
    second = Audit.projectedOrderedTerm system (Symmetry.swapTriad tau)
    residual = externalResidualVector system tau tauMember swapMember swapDifferent
  in
  trans
    (fullOutputFibreIsTwoSelectedTermsPlusResidual
      system tau tauMember swapMember swapDifferent)
    (trans
      (sym (Algebra.complex3AddAssociative first second residual))
      (cong
        (λ self → C3.complex3Add self residual)
        (sym (selfForcingKIsTwoSelectedOrderedTerms system tau))))

subtractSelfFromSelfPlusResidual :
  ∀ {r} {F : C3.RealField r}
    (self residual : C3.Complex3 F) →
  C3.complex3Subtract (C3.complex3Add self residual) self ≡ residual
subtractSelfFromSelfPlusResidual {F = F}
    (C3.complex3 sx sy sz) (C3.complex3 rx ry rz) =
  Algebra.complex3Ext
    (R.solve 2 (λ s r → ((s R.⊕ r) R.⊕ (R.⊝ s)) R.⊜ r) refl sx rx)
    (R.solve 2 (λ s r → ((s R.⊕ r) R.⊕ (R.⊝ s)) R.⊜ r) refl sy ry)
    (R.solve 2 (λ s r → ((s R.⊕ r) R.⊕ (R.⊝ s)) R.⊜ r) refl sz rz)
  where module R = Ring.Solver F

externalForcingKIsSelfOrbitRemovedOutputFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  Split.externalForcingK system tau
  ≡ externalResidualVector system tau tauMember swapMember swapDifferent
externalForcingKIsSelfOrbitRemovedOutputFibre
    system tau tauMember swapMember swapDifferent =
  trans
    (cong
      (λ full → C3.complex3Subtract full (Split.selfForcingK system tau))
      (fullForcingKIsSelfPlusResidualCarrier
        system tau tauMember swapMember swapDifferent))
    (subtractSelfFromSelfPlusResidual
      (Split.selfForcingK system tau)
      (externalResidualVector system tau tauMember swapMember swapDifferent))

round111ExternalForcingIsSelfOrbitRemovedOutputFibre : Bool
round111ExternalForcingIsSelfOrbitRemovedOutputFibre = true

round111ExternalCarrierKeepsLiteralOutputFibreTerms : Bool
round111ExternalCarrierKeepsLiteralOutputFibreTerms = true

round111ExternalForcingIsSelfOrbitRemovedOutputFibreIsTrue :
  round111ExternalForcingIsSelfOrbitRemovedOutputFibre ≡ true
round111ExternalForcingIsSelfOrbitRemovedOutputFibreIsTrue = refl

round111ExternalCarrierKeepsLiteralOutputFibreTermsIsTrue :
  round111ExternalCarrierKeepsLiteralOutputFibreTerms ≡ true
round111ExternalCarrierKeepsLiteralOutputFibreTermsIsTrue = refl
