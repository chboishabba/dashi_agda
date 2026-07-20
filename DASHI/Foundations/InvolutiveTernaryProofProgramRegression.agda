module DASHI.Foundations.InvolutiveTernaryProofProgramRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as T
import DASHI.Algebra.TernaryComposition as A
import DASHI.Foundations.InvolutiveTernaryExistingSpineBridge as Spine
import DASHI.Foundations.TernaryBlockRenormalisation as Block
import DASHI.Foundations.DefectValuedCommutation as Defect
import DASHI.Foundations.ActionMDLSeparation as MDL
import DASHI.Foundations.FiniteInvolutiveTrajectory as Path
import DASHI.Foundations.InvariantTransportTower as Invariant
import DASHI.Foundations.FiniteAdmissibleCoding as Coding
import DASHI.Foundations.EquivariantResidual as Residual

------------------------------------------------------------------------
-- Compact import/regression surface for the completed generic proof-programme
-- tranche.  The fields are concrete theorem witnesses where a canonical
-- instance exists and explicit carrier contracts where an application must
-- still choose data.

record ProofProgramReceipt : Set₁ where
  constructor receipt
  field
    existingSpineRecovered : Spine.ExistingSpineBridgeReceipt
    saturatingOppositesCancel : ∀ x → x A.⊕ T.inv x ≡ T.zer
    exactCarryOppositesCancel : ∀ x →
      A.addCarry x (T.inv x) ≡ A.dc T.zer T.zer
    threeToOneBlockRecorded : Block.TernaryBlockReceipt

    defectContractAvailable : Set₁
    mdlSeparationAvailable : Set₁
    finitePathContractAvailable : Set₁
    invariantTransportAvailable : Set₁
    finiteCodingAvailable : Set₁
    equivariantResidualAvailable : Set₁

proofProgramReceipt : ProofProgramReceipt
proofProgramReceipt =
  receipt
    Spine.existingSpineBridgeReceipt
    A.opposites-cancel
    A.addCarry-opposites
    Block.ternaryBlockReceipt
    Defect.DefectValuedCommutation
    MDL.DescriptionLength
    Path.FinitePath
    Invariant.TransportedInvariantTower
    Coding.FiniteAdmissibleCode
    Residual.EquivariantResidual
