{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalSelfOrbitMultiplicityRound618Exact where

------------------------------------------------------------------------
-- ROUND618 / EXTERNAL SELF-ORBIT MULTIPLICITY: FIXED VS NONFIXED
--
-- R111 represents external forcing by deleting tau and swap(tau) when those
-- are distinct members of the literal output fibre.
--
-- At a swap-fixed incidence the duplicate-free fibre contains tau only once,
-- but the selected self forcing still contains TWO ordered placements:
--
--   Self(tau) = Term(tau) + Term(swap tau) = 2 Term(tau).
--
-- Hence deleting tau once is not enough.  If
--
--   Full = Term(tau) + Residual,
--
-- then
--
--   External = Full - Self = Residual - Term(tau).
--
-- This module proves that correction exactly and packages both orbit cases in
-- one proof-relevant carrier.  No estimate or cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
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
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111

------------------------------------------------------------------------
-- Fixed-orbit residual carrier.
------------------------------------------------------------------------

fixedResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  List Physical.PhysicalTriadIncidence
fixedResidualCarrier system tau tauMember =
  Fibre.removeAt tauMember

fixedResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  C3.Complex3 F
fixedResidualVector system tau tauMember =
  Audit.sumVectors
    (Audit.mapTriadTerms system
      (fixedResidualCarrier system tau tauMember))

fullOutputFibreIsSelectedPlusFixedResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  Audit.projectedNonlinearity system (Physical.k tau)
  ≡
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (fixedResidualVector system tau tauMember)
fullOutputFibreIsSelectedPlusFixedResidual system tau tauMember =
  Sum.sumVectorsRespPermutation
    (Sum.mapTriadTermsRespPermutation system
      (Fibre.removeAtPermutation tauMember))

selfForcingKAtSwapFixed :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Symmetry.swapTriad tau ≡ tau →
  Split.selfForcingK system tau
  ≡
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (Audit.projectedOrderedTerm system tau)
selfForcingKAtSwapFixed system tau fixed =
  cong
    (C3.complex3Add (Audit.projectedOrderedTerm system tau))
    (cong (Audit.projectedOrderedTerm system) fixed)

subtractDoubleSelectedFromSelectedPlusResidual :
  ∀ {r} {F : C3.RealField r}
    (selected residual : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Add selected residual)
    (C3.complex3Add selected selected)
  ≡
  C3.complex3Subtract residual selected
subtractDoubleSelectedFromSelectedPlusResidual {F = F}
    (C3.complex3 sx sy sz)
    (C3.complex3 rx ry rz) =
  Algebra.complex3Ext
    (R.solve 2
      (λ s r →
        ((s R.⊕ r) R.⊕ (R.⊝ (s R.⊕ s)))
        R.⊜
        (r R.⊕ (R.⊝ s)))
      refl sx rx)
    (R.solve 2
      (λ s r →
        ((s R.⊕ r) R.⊕ (R.⊝ (s R.⊕ s)))
        R.⊜
        (r R.⊕ (R.⊝ s)))
      refl sy ry)
    (R.solve 2
      (λ s r →
        ((s R.⊕ r) R.⊕ (R.⊝ (s R.⊕ s)))
        R.⊜
        (r R.⊕ (R.⊝ s)))
      refl sz rz)
  where module R = Ring.Solver F

externalForcingKAtSwapFixed :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (fixed : Symmetry.swapTriad tau ≡ tau) →
  Split.externalForcingK system tau
  ≡
  C3.complex3Subtract
    (fixedResidualVector system tau tauMember)
    (Audit.projectedOrderedTerm system tau)
externalForcingKAtSwapFixed system tau tauMember fixed =
  trans
    (cong
      (λ full →
        C3.complex3Subtract full (Split.selfForcingK system tau))
      (fullOutputFibreIsSelectedPlusFixedResidual
        system tau tauMember))
    (trans
      (cong
        (C3.complex3Subtract
          (C3.complex3Add
            (Audit.projectedOrderedTerm system tau)
            (fixedResidualVector system tau tauMember)))
        (selfForcingKAtSwapFixed system tau fixed))
      (subtractDoubleSelectedFromSelectedPlusResidual
        (Audit.projectedOrderedTerm system tau)
        (fixedResidualVector system tau tauMember)))

------------------------------------------------------------------------
-- Total proof-relevant self-orbit representation.
------------------------------------------------------------------------

data SwapOrbitCase
    (tau : Physical.PhysicalTriadIncidence) : Set where
  nonfixed :
    Symmetry.swapTriad tau ≢ tau →
    SwapOrbitCase tau
  fixed :
    Symmetry.swapTriad tau ≡ tau →
    SwapOrbitCase tau

orbitResolvedExternalVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  SwapOrbitCase tau →
  C3.Complex3 F
orbitResolvedExternalVector system tau tauMember (nonfixed different) =
  R111.externalResidualVector system tau tauMember
    (DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.swapOutputFibreMember tauMember)
    different
orbitResolvedExternalVector system tau tauMember (fixed equality) =
  C3.complex3Subtract
    (fixedResidualVector system tau tauMember)
    (Audit.projectedOrderedTerm system tau)

externalForcingKIsOrbitResolved :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (orbitCase : SwapOrbitCase tau) →
  Split.externalForcingK system tau
  ≡ orbitResolvedExternalVector system tau tauMember orbitCase
externalForcingKIsOrbitResolved system tau tauMember (nonfixed different) =
  R111.externalForcingKIsSelfOrbitRemovedOutputFibre
    system tau tauMember
    (DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.swapOutputFibreMember tauMember)
    different
externalForcingKIsOrbitResolved system tau tauMember (fixed equality) =
  externalForcingKAtSwapFixed system tau tauMember equality

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round618FixedOrbitCorrectionClosed : Bool
round618FixedOrbitCorrectionClosed = true

round618NonfixedOrbitRecoversR111 : Bool
round618NonfixedOrbitRecoversR111 = true

round618ExternalForcingHasTotalProofRelevantOrbitRepresentation : Bool
round618ExternalForcingHasTotalProofRelevantOrbitRepresentation = true

round618FixedOrbitResidualIsPlainDeletionOnly : Bool
round618FixedOrbitResidualIsPlainDeletionOnly = false

round618IntroducesEstimate : Bool
round618IntroducesEstimate = false

round618FixedOrbitCorrectionClosedIsTrue :
  round618FixedOrbitCorrectionClosed ≡ true
round618FixedOrbitCorrectionClosedIsTrue = refl

round618NonfixedOrbitRecoversR111IsTrue :
  round618NonfixedOrbitRecoversR111 ≡ true
round618NonfixedOrbitRecoversR111IsTrue = refl

round618ExternalForcingHasTotalProofRelevantOrbitRepresentationIsTrue :
  round618ExternalForcingHasTotalProofRelevantOrbitRepresentation ≡ true
round618ExternalForcingHasTotalProofRelevantOrbitRepresentationIsTrue = refl

round618FixedOrbitResidualIsPlainDeletionOnlyIsFalse :
  round618FixedOrbitResidualIsPlainDeletionOnly ≡ false
round618FixedOrbitResidualIsPlainDeletionOnlyIsFalse = refl

round618IntroducesEstimateIsFalse :
  round618IntroducesEstimate ≡ false
round618IntroducesEstimateIsFalse = refl
