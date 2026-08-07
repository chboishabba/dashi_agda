module DASHI.Papers.NavierStokes.ClayContractRound23 where

------------------------------------------------------------------------
-- Paper-facing status surface for the literal periodic Clay contract.
--
-- The official Fefferman alternative (B) theorem type is now represented
-- exactly.  The end-to-end repository composition is connected.  Physical
-- producer inhabitation and unconditional theorem promotion remain false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoClayPrePostInvariantContractRound23Exact as Contract
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as EndToEnd

record NSClayContractRound23Status : Set where
  constructor nsClayContractRound23Status
  field
    literalFeffermanPeriodicStatementImplemented : Bool
    exactPreconditionsImplemented : Bool
    exactPostconditionsImplemented : Bool
    proofRouteInvariantsImplemented : Bool
    endToEndCompositionImplemented : Bool
    physicalProducersInhabited : Bool
    unconditionalClayTheoremPromoted : Bool

open NSClayContractRound23Status public

canonicalNSClayContractRound23Status : NSClayContractRound23Status
canonicalNSClayContractRound23Status =
  nsClayContractRound23Status true true true true true false false

literalTargetIsImplemented :
  literalFeffermanPeriodicStatementImplemented
    canonicalNSClayContractRound23Status
  ≡ true
literalTargetIsImplemented = refl

physicalProducersRemainOpen :
  physicalProducersInhabited canonicalNSClayContractRound23Status ≡ false
physicalProducersRemainOpen = refl

clayPromotionRemainsFalse :
  unconditionalClayTheoremPromoted canonicalNSClayContractRound23Status
  ≡ false
clayPromotionRemainsFalse = refl

literalRequirementAudit : Clay.FeffermanPeriodicRequirementAudit
literalRequirementAudit = Clay.canonicalFeffermanPeriodicRequirementAudit

preconditions : Contract.ClayPreconditions
preconditions = Contract.canonicalClayPreconditions

postconditions : Contract.ClayPostconditions
postconditions = Contract.canonicalClayPostconditions

invariants : Contract.ProofRouteInvariants
invariants = Contract.canonicalProofRouteInvariants

pathState : Contract.InRepoPathState
pathState = Contract.canonicalInRepoPathState

endToEndBoundary : EndToEnd.ClayEndToEndAuthorityBoundary
endToEndBoundary = EndToEnd.canonicalClayEndToEndAuthorityBoundary
