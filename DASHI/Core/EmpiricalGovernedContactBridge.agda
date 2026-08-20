module DASHI.Core.EmpiricalGovernedContactBridge where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.EmpiricalContactReceipt as Empirical
import DASHI.Core.GovernedContactCore as Governed
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.ReplayArtifactCore as Replay

------------------------------------------------------------------------
-- Empirical receipts are late specializations of governed contact.
--
-- The bridge is intentionally proof-bearing: callers must supply the exact
-- residual encoder connecting the receipt's projected residual family to the
-- Hamiltonian residual carrier, together with replay and gate witnesses.
------------------------------------------------------------------------

empiricalReceiptGivesGovernedContact :
  (receipt : Empirical.EmpiricalContactReceipt) →
  ({left right : Geometry.Observable (Empirical.contactGeometry receipt)} →
    Geometry.Residual (Empirical.contactGeometry receipt) left right →
    Hamiltonian.Residual (Empirical.contactHamiltonian receipt)) →
  Replay.replayable (Empirical.replay receipt) ≡ true →
  Replay.replayPromotesTruth (Empirical.replay receipt) ≡ false →
  Gate.promotesTruth (Empirical.contactGateCore receipt) ≡ false →
  Governed.GovernedContactCore
empiricalReceiptGivesGovernedContact receipt residualEncode replayLive replayNonPromoting gateClosed =
  Governed.governedContactCore
    (Empirical.contactGeometry receipt)
    (Empirical.contactHamiltonian receipt)
    (Empirical.replay receipt)
    (Empirical.contactGateCore receipt)
    residualEncode
    replayLive
    replayNonPromoting
    gateClosed
