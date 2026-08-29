module DASHI.Physics.Closure.NSTriadKNExternalResidualReciprocityRound117Exact where

------------------------------------------------------------------------
-- ROUND117 / RECIPROCITY OF SELF-ORBIT-REMOVED OUTPUT-FIBRE MEMBERSHIP
--
-- Round116 identified the correct quartet partner as cross-selected exchange
-- (tau,sigma) <-> (sigma,tau).  The immediate combinatorial question is whether
-- a one-sided external residual cell automatically survives in the reverse
-- selected residual.
--
-- It does, once BOTH incidences are legitimate non-swap-fixed selections in
-- their common output fibre.  If sigma survives deletion of tau and swap(tau),
-- uniqueness implies sigma != tau and sigma != swap(tau).  Swap involutivity
-- converts the latter into tau != swap(sigma), so tau survives deletion of
-- sigma and swap(sigma).
--
-- This closes the mutual-residual combinatorial seam with no cardinality loss.
-- The remaining issue is now analytic/algebraic: evaluate the literal
-- cross-selected Waleffe defect on these reciprocal pairs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as Residual
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeCrossSelectedPartnerRound116Exact as R116

residualMemberReturnsToOriginalFibre :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (S : R116.KResidualSelection system tau) →
  sigma ∈ R116.kResidualCarrier system tau S →
  sigma ∈ Audit.concreteTriadsAt system (Physical.k tau)
residualMemberReturnsToOriginalFibre system tau sigma S sigmaResidual =
  KFree.removeAtMemberOriginal
    (R116.selectedMember S)
    (KFree.removeAtMemberOriginal
      (KFree.otherMemberSurvivesRemoval
        (R116.selectedMember S)
        (R116.selectedSwapMember S)
        (R116.selectedSwapDifferent S))
      sigmaResidual)

residualMemberDifferentFromSelected :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (S : R116.KResidualSelection system tau) →
  sigma ∈ R116.kResidualCarrier system tau S →
  sigma ≢ tau
residualMemberDifferentFromSelected system tau sigma S sigmaResidual equality =
  let
    originalUnique =
      KFree.physicalOutputFiberUnique
        (Audit.cutoff system) (Physical.k tau)
    afterTauMember =
      KFree.removeAtMemberOriginal
        (KFree.otherMemberSurvivesRemoval
          (R116.selectedMember S)
          (R116.selectedSwapMember S)
          (R116.selectedSwapDifferent S))
        sigmaResidual
    tauFresh =
      KFree.removedElementFresh originalUnique (R116.selectedMember S)
  in
  tauFresh
    (subst
      (λ chosen → chosen ∈ KFree.removeAt (R116.selectedMember S))
      equality
      afterTauMember)

residualMemberDifferentFromSelectedSwap :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (S : R116.KResidualSelection system tau) →
  sigma ∈ R116.kResidualCarrier system tau S →
  sigma ≢ Symmetry.swapTriad tau
residualMemberDifferentFromSelectedSwap system tau sigma S sigmaResidual equality =
  let
    originalUnique =
      KFree.physicalOutputFiberUnique
        (Audit.cutoff system) (Physical.k tau)
    swapSurvives =
      KFree.otherMemberSurvivesRemoval
        (R116.selectedMember S)
        (R116.selectedSwapMember S)
        (R116.selectedSwapDifferent S)
    afterTauUnique =
      KFree.removeAtUnique originalUnique (R116.selectedMember S)
    swapFresh = KFree.removedElementFresh afterTauUnique swapSurvives
  in
  swapFresh
    (subst
      (λ chosen → chosen ∈ KFree.removeAt swapSurvives)
      equality
      sigmaResidual)

tauDifferentFromSwapSigma :
  ∀ {tau sigma : Physical.PhysicalTriadIncidence} →
  sigma ≢ Symmetry.swapTriad tau →
  tau ≢ Symmetry.swapTriad sigma
tauDifferentFromSwapSigma sigmaNotSwapTau tauEqualsSwapSigma =
  sigmaNotSwapTau
    (sym
      (trans
        (cong Symmetry.swapTriad tauEqualsSwapSigma)
        (Round38.swapTriadInvolutiveExact sigma)))

reverseOriginalFibreMembership :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (Sτ : R116.KResidualSelection system tau) →
  sigma ∈ R116.kResidualCarrier system tau Sτ →
  tau ∈ Audit.concreteTriadsAt system (Physical.k sigma)
reverseOriginalFibreMembership system tau sigma Sτ sigmaResidual =
  let
    sigmaOriginal =
      residualMemberReturnsToOriginalFibre system tau sigma Sτ sigmaResidual
    outputEquality = Audit.concreteTriadsAtOutputAgreement sigmaOriginal
  in
  subst
    (λ output → tau ∈ Audit.concreteTriadsAt system output)
    (sym outputEquality)
    (R116.selectedMember Sτ)

oneSidedResidualPromotesToReverseResidual :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (Sτ : R116.KResidualSelection system tau)
    (Sσ : R116.KResidualSelection system sigma) →
  sigma ∈ R116.kResidualCarrier system tau Sτ →
  tau ∈ R116.kResidualCarrier system sigma Sσ
oneSidedResidualPromotesToReverseResidual system tau sigma Sτ Sσ sigmaResidual =
  let
    tauInSigmaFibre =
      reverseOriginalFibreMembership system tau sigma Sτ sigmaResidual
    sigmaNotTau =
      residualMemberDifferentFromSelected system tau sigma Sτ sigmaResidual
    tauNotSigma : tau ≢ sigma
    tauNotSigma equality = sigmaNotTau (sym equality)
    sigmaNotSwapTau =
      residualMemberDifferentFromSelectedSwap system tau sigma Sτ sigmaResidual
    tauNotSwapSigma = tauDifferentFromSwapSigma sigmaNotSwapTau
    tauAfterSigma =
      KFree.otherMemberSurvivesRemoval
        (R116.selectedMember Sσ)
        tauInSigmaFibre
        tauNotSigma
    swapSigmaSurvives =
      KFree.otherMemberSurvivesRemoval
        (R116.selectedMember Sσ)
        (R116.selectedSwapMember Sσ)
        (R116.selectedSwapDifferent Sσ)
  in
  KFree.otherMemberSurvivesRemoval
    swapSigmaSurvives
    tauAfterSigma
    tauNotSwapSigma

promoteToMutualKResidualCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence)
    (Sτ : R116.KResidualSelection system tau)
    (Sσ : R116.KResidualSelection system sigma) →
  sigma ∈ R116.kResidualCarrier system tau Sτ →
  R116.MutualKResidualCell system
promoteToMutualKResidualCell system tau sigma Sτ Sσ sigmaResidual =
  R116.mutual-k-residual-cell
    tau sigma Sτ Sσ sigmaResidual
    (oneSidedResidualPromotesToReverseResidual
      system tau sigma Sτ Sσ sigmaResidual)

round117ResidualReciprocityClosed : Bool
round117ResidualReciprocityClosed = true

round117OneSidedCellPromotesGivenReverseSelection : Bool
round117OneSidedCellPromotesGivenReverseSelection = true

round117CrossSelectedDefectSimplifiedOrPaid : Bool
round117CrossSelectedDefectSimplifiedOrPaid = false

round117ResidualReciprocityClosedIsTrue :
  round117ResidualReciprocityClosed ≡ true
round117ResidualReciprocityClosedIsTrue = refl

round117OneSidedCellPromotesGivenReverseSelectionIsTrue :
  round117OneSidedCellPromotesGivenReverseSelection ≡ true
round117OneSidedCellPromotesGivenReverseSelectionIsTrue = refl

round117CrossSelectedDefectSimplifiedOrPaidIsFalse :
  round117CrossSelectedDefectSimplifiedOrPaid ≡ false
round117CrossSelectedDefectSimplifiedOrPaidIsFalse = refl
