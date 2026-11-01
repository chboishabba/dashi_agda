module DASHI.Physics.Closure.NSTriadKNExternalResidualPositiveMajorantRestrictionRound112Exact where

------------------------------------------------------------------------
-- ROUND112 / POSITIVE MAJORANTS DO NOT PAY A SELF-ORBIT REMOVAL TAX
--
-- Round111 identifies the external carrier by deleting two selected ordered
-- incidences from one literal output fibre.  For any nonnegative rational
-- majorant m(tau), deletion can only decrease the finite sum:
--
--   sum_residual m <= sum_full-fibre m.
--
-- This is deliberately a POSITIVE-majorant theorem.  It does not assert
-- monotonicity for the signed commutator sum, where cancellation matters and
-- must be exposed before absolute values.  Its purpose is to show that the
-- far-high/paraproduct and comparable/local positive estimates incur no new
-- combinatorial or cutoff constant merely because the selected self orbit was
-- removed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≢_; subst)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Fibre
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as External

sumMajorant :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
sumMajorant value [] = 0ℚ
sumMajorant value (tau ∷ rest) = value tau + sumMajorant value rest

sumMajorantNonnegative :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) → 0ℚ ≤ value tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  0ℚ ≤ sumMajorant value items
sumMajorantNonnegative value valueNN [] = ℚP.≤-refl
sumMajorantNonnegative value valueNN (tau ∷ rest) =
  ℚP.+-mono-≤ (valueNN tau) (sumMajorantNonnegative value valueNN rest)

sumRemoveAtBelowOriginal :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) → 0ℚ ≤ value tau) →
  ∀ {selected items} →
  (membership : selected ∈ items) →
  sumMajorant value (Fibre.removeAt membership)
  ≤ sumMajorant value items
sumRemoveAtBelowOriginal value valueNN (Any.here refl) =
  subst
    (λ lower → lower ≤ value _ + sumMajorant value _)
    (ℚP.+-identityˡ (sumMajorant value _))
    (ℚP.+-mono-≤ (valueNN _) ℚP.≤-refl)
sumRemoveAtBelowOriginal value valueNN (Any.there membership) =
  ℚP.+-mono-≤ ℚP.≤-refl
    (sumRemoveAtBelowOriginal value valueNN membership)

externalResidualMajorantBelowFullOutputFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau)
    (majorant : Physical.PhysicalTriadIncidence → ℚ)
    (majorantNN : (cell : Physical.PhysicalTriadIncidence) →
      0ℚ ≤ majorant cell) →
  sumMajorant majorant
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)
  ≤
  sumMajorant majorant
    (Audit.concreteTriadsAt system (Physical.k tau))
externalResidualMajorantBelowFullOutputFibre
    system tau tauMember swapMember swapDifferent majorant majorantNN =
  let
    swapSurvives =
      Fibre.otherMemberSurvivesRemoval tauMember swapMember swapDifferent
    secondRemoval :
      sumMajorant majorant
        (Fibre.removeAt swapSurvives)
      ≤
      sumMajorant majorant (Fibre.removeAt tauMember)
    secondRemoval =
      sumRemoveAtBelowOriginal majorant majorantNN swapSurvives
    firstRemoval :
      sumMajorant majorant (Fibre.removeAt tauMember)
      ≤
      sumMajorant majorant
        (Audit.concreteTriadsAt system (Physical.k tau))
    firstRemoval =
      sumRemoveAtBelowOriginal majorant majorantNN tauMember
  in
  ℚP.≤-trans secondRemoval firstRemoval

round112ExternalPositiveMajorantRestrictionClosed : Bool
round112ExternalPositiveMajorantRestrictionClosed = true

round112SelfOrbitRemovalAddsNoPositiveMajorantCutoffTax : Bool
round112SelfOrbitRemovalAddsNoPositiveMajorantCutoffTax = true

round112ExternalPositiveMajorantRestrictionClosedIsTrue :
  round112ExternalPositiveMajorantRestrictionClosed ≡ true
round112ExternalPositiveMajorantRestrictionClosedIsTrue = refl

round112SelfOrbitRemovalAddsNoPositiveMajorantCutoffTaxIsTrue :
  round112SelfOrbitRemovalAddsNoPositiveMajorantCutoffTax ≡ true
round112SelfOrbitRemovalAddsNoPositiveMajorantCutoffTaxIsTrue = refl
