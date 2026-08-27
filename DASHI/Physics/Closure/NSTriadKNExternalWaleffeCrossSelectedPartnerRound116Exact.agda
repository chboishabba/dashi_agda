module DASHI.Physics.Closure.NSTriadKNExternalWaleffeCrossSelectedPartnerRound116Exact where

------------------------------------------------------------------------
-- ROUND116 / ACTUAL CROSS-SELECTED PARTNER ON K-SLOT WALEFFE CELLS
--
-- Round115 expands the true external Waleffe forcing into incidence cells.
-- A crucial scope correction follows immediately from the cell geometry.
--
-- A K-slot cell is indexed by TWO physical triads with the same output:
--
--   selected tau : p_tau + q_tau = k,
--   forcing  sigma: p_sigma + q_sigma = k,
--
-- and has literal value
--
--   T(tau,sigma)
--     = < projectedOrderedTerm(sigma), u_p(tau) x u_q(tau) >.
--
-- Therefore the natural quartet partner is NOT a reality mate and not the
-- p/q swap inside one selected triad.  It is the cross-selected exchange
--
--   (tau,sigma) |-> (sigma,tau),
--
-- whenever each incidence survives deletion of the other's self swap-orbit.
-- This module constructs that partner on the ACTUAL mutual residual carrier,
-- proves the transfer is involutive under two exchanges, and defines/evaluates
-- the literal antisymmetry defect
--
--   R(tau,sigma) = T(sigma,tau) + T(tau,sigma).
--
-- No claim that R=0 is made.  The next hard theorem is now exact: promote the
-- one-sided Round115 residual cells to this mutual carrier (up to explicitly
-- supported occupation/boundary exceptions), then simplify/pay R.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as Residual
import DASHI.Physics.Closure.NSTriadKNExternalSharedModeAntisymmetryDefectRound114Exact as Defect

record KResidualSelection
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    selectedMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)
    selectedSwapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau)
    selectedSwapDifferent : Symmetry.swapTriad tau ≢ tau

open KResidualSelection public

kResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  KResidualSelection system tau →
  List Physical.PhysicalTriadIncidence
kResidualCarrier system tau S =
  Residual.externalResidualCarrier system tau
    (selectedMember S) (selectedSwapMember S) (selectedSwapDifferent S)

record MutualKResidualCell
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) : Set where
  constructor mutual-k-residual-cell
  field
    leftSelected rightSelected : Physical.PhysicalTriadIncidence
    leftSelection : KResidualSelection system leftSelected
    rightSelection : KResidualSelection system rightSelected
    rightInLeftResidual :
      rightSelected ∈ kResidualCarrier system leftSelected leftSelection
    leftInRightResidual :
      leftSelected ∈ kResidualCarrier system rightSelected rightSelection

open MutualKResidualCell public

crossSelectedPartner :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  MutualKResidualCell system → MutualKResidualCell system
crossSelectedPartner X =
  mutual-k-residual-cell
    (rightSelected X)
    (leftSelected X)
    (rightSelection X)
    (leftSelection X)
    (leftInRightResidual X)
    (rightInLeftResidual X)

kWaleffeCrossCellTransfer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → C3.Complex F
kWaleffeCrossCellTransfer system selected forcing =
  C3.hermitianPairing3
    (Audit.projectedOrderedTerm system forcing)
    (Cross.complex3Cross
      (Audit.velocity system (Physical.p selected))
      (Audit.velocity system (Physical.q selected)))

mutualCellTransfer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  MutualKResidualCell system → C3.Complex F
mutualCellTransfer system X =
  kWaleffeCrossCellTransfer system (leftSelected X) (rightSelected X)

partnerTransfer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  MutualKResidualCell system → C3.Complex F
partnerTransfer system X = mutualCellTransfer system (crossSelectedPartner X)

crossSelectedPartnerTransferIsLiteralExchange :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (X : MutualKResidualCell system) →
  partnerTransfer system X
  ≡ kWaleffeCrossCellTransfer system (rightSelected X) (leftSelected X)
crossSelectedPartnerTransferIsLiteralExchange system X = refl

crossSelectedPartnerTwiceRestoresTransfer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (X : MutualKResidualCell system) →
  mutualCellTransfer system (crossSelectedPartner (crossSelectedPartner X))
  ≡ mutualCellTransfer system X
crossSelectedPartnerTwiceRestoresTransfer system X = refl

literalCrossSelectedDefect :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  MutualKResidualCell system → C3.Complex F
literalCrossSelectedDefect system X =
  Defect.antisymmetryDefect
    (mutualCellTransfer system X)
    (partnerTransfer system X)

literalCrossSelectedDefectEvaluatesToTwoActualWaleffeCells :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (X : MutualKResidualCell system) →
  literalCrossSelectedDefect system X
  ≡ C3.complexAdd
      (kWaleffeCrossCellTransfer system (rightSelected X) (leftSelected X))
      (kWaleffeCrossCellTransfer system (leftSelected X) (rightSelected X))
literalCrossSelectedDefectEvaluatesToTwoActualWaleffeCells system X = refl

round116ActualCrossSelectedPartnerConstructed : Bool
round116ActualCrossSelectedPartnerConstructed = true

round116LiteralCrossSelectedDefectEvaluated : Bool
round116LiteralCrossSelectedDefectEvaluated = true

round116EveryOneSidedResidualCellPromotedToMutualCarrier : Bool
round116EveryOneSidedResidualCellPromotedToMutualCarrier = false

round116CrossSelectedDefectProvedZeroOrPaid : Bool
round116CrossSelectedDefectProvedZeroOrPaid = false

round116ActualCrossSelectedPartnerConstructedIsTrue :
  round116ActualCrossSelectedPartnerConstructed ≡ true
round116ActualCrossSelectedPartnerConstructedIsTrue = refl

round116LiteralCrossSelectedDefectEvaluatedIsTrue :
  round116LiteralCrossSelectedDefectEvaluated ≡ true
round116LiteralCrossSelectedDefectEvaluatedIsTrue = refl

round116EveryOneSidedResidualCellPromotedToMutualCarrierIsFalse :
  round116EveryOneSidedResidualCellPromotedToMutualCarrier ≡ false
round116EveryOneSidedResidualCellPromotedToMutualCarrierIsFalse = refl

round116CrossSelectedDefectProvedZeroOrPaidIsFalse :
  round116CrossSelectedDefectProvedZeroOrPaid ≡ false
round116CrossSelectedDefectProvedZeroOrPaidIsFalse = refl
