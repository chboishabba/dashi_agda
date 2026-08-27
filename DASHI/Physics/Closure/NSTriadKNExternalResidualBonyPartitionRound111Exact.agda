module DASHI.Physics.Closure.NSTriadKNExternalResidualBonyPartitionRound111Exact where

------------------------------------------------------------------------
-- ROUND111 / BONY ROUTING OF THE SELF-ORBIT-REMOVED EXTERNAL CARRIER
--
-- The Round63 Bony classifier and filter lemmas are generic over arbitrary
-- incidence lists.  Apply them directly to the Round111 external residual
-- carrier.  Every surviving cross-triad incidence lies in exactly one of
--
--   LH, HL, HH->low, comparable.
--
-- Thus no new external-network frequency taxonomy is required.  The live
-- analytic work is the same-object quantitative estimate on these residual
-- class lists, with the far-low class first exposing the Round62 commutator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as External

externalBonyResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (tag : Bony.BonyTag)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  List Physical.PhysicalTriadIncidence
externalBonyResidual tag system tau tauMember swapMember swapDifferent =
  Bony.filterBonyTag tag
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

externalResidualMemberRouted :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau incidence : Physical.PhysicalTriadIncidence}
    {tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)}
    {swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau)}
    {swapDifferent : Symmetry.swapTriad tau ≢ tau} →
  incidence Cube.∈
    External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent →
  (incidence Cube.∈ externalBonyResidual
      Bony.lhTag system tau tauMember swapMember swapDifferent)
  ⊎ ((incidence Cube.∈ externalBonyResidual
      Bony.hlTag system tau tauMember swapMember swapDifferent)
  ⊎ ((incidence Cube.∈ externalBonyResidual
      Bony.hhToLowTag system tau tauMember swapMember swapDifferent)
  ⊎  (incidence Cube.∈ externalBonyResidual
      Bony.comparableTag system tau tauMember swapMember swapDifferent)))
externalResidualMemberRouted {incidence = incidence} member
  with Bony.bonyTag incidence
... | Bony.lhTag = inj₁ (Bony.filterTagMemberComplete member refl)
... | Bony.hlTag = inj₂ (inj₁ (Bony.filterTagMemberComplete member refl))
... | Bony.hhToLowTag =
      inj₂ (inj₂ (inj₁ (Bony.filterTagMemberComplete member refl)))
... | Bony.comparableTag =
      inj₂ (inj₂ (inj₂ (Bony.filterTagMemberComplete member refl)))

externalResidualMemberCannotHaveTwoDistinctTags :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau incidence : Physical.PhysicalTriadIncidence}
    {tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)}
    {swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau)}
    {swapDifferent : Symmetry.swapTriad tau ≢ tau}
    {left right : Bony.BonyTag} →
  incidence Cube.∈ externalBonyResidual
    left system tau tauMember swapMember swapDifferent →
  incidence Cube.∈ externalBonyResidual
    right system tau tauMember swapMember swapDifferent →
  left ≡ right
externalResidualMemberCannotHaveTwoDistinctTags leftMember rightMember =
  trans
    (sym (Bony.filterTagMemberSound leftMember))
    (Bony.filterTagMemberSound rightMember)

round111ExternalResidualBonyPartitionClosed : Bool
round111ExternalResidualBonyPartitionClosed = true

round111ExternalResidualNeedsNoNewFrequencyTaxonomy : Bool
round111ExternalResidualNeedsNoNewFrequencyTaxonomy = true

round111ExternalResidualBonyPartitionClosedIsTrue :
  round111ExternalResidualBonyPartitionClosed ≡ true
round111ExternalResidualBonyPartitionClosedIsTrue = refl

round111ExternalResidualNeedsNoNewFrequencyTaxonomyIsTrue :
  round111ExternalResidualNeedsNoNewFrequencyTaxonomy ≡ true
round111ExternalResidualNeedsNoNewFrequencyTaxonomyIsTrue = refl
