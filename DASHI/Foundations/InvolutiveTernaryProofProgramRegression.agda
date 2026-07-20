module DASHI.Foundations.InvolutiveTernaryProofProgramRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Algebra.Trit as T
import DASHI.Algebra.TernaryComposition as A
import DASHI.Foundations.InvolutiveTernaryExistingSpineBridge as Spine
import DASHI.Foundations.TernaryBlockRenormalisation as Block
import DASHI.Foundations.DefectValuedCommutation
import DASHI.Foundations.ActionMDLSeparation
import DASHI.Foundations.FiniteInvolutiveTrajectory
import DASHI.Foundations.InvariantTransportTower
import DASHI.Foundations.FiniteAdmissibleCoding
import DASHI.Foundations.EquivariantResidual

record ProofProgramReceipt : Set₁ where
  constructor receipt
  field
    existingSpineRecovered : Spine.ExistingSpineBridgeReceipt
    saturatingOppositesCancel : ∀ x → x A.⊕ T.inv x ≡ T.zer
    exactCarryOppositesCancel : ∀ x →
      A.addCarry x (T.inv x) ≡ A.dc T.zer T.zer
    threeToOneBlockRecorded : Block.TernaryBlockReceipt

proofProgramReceipt : ProofProgramReceipt
proofProgramReceipt =
  receipt
    Spine.existingSpineBridgeReceipt
    A.opposites-cancel
    A.addCarry-opposites
    Block.ternaryBlockReceipt
