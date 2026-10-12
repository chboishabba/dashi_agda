module DASHI.Moonshine.MonsterOgg279CMObserverCompletionExact where

------------------------------------------------------------------------
-- COMPLETION OF THE p31 CM OBSERVER SURFACE AROUND THE MERGED 279 HUB
--
-- The merged hub already imports the CM receipt module and records the p31
-- Ogg/nonary/rank/FRACTRAN projections.  This small owner closes the one
-- documented source/source mismatch: p31 is also literally inert in the
-- existing Q(sqrt(-7)) CM observer.  It adds no new 279 semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.MonsterOgg279ProvenanceHubExact as Hub
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Affine
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

p31CMClassIsInert :
  Affine.cmClass Lane.p31 ≡ CM.inert
p31CMClassIsInert = refl

-- The theorem is explicitly about another observer of the already-selected
-- p31 lane.  It does not alter the role firewall in Hub.Role279.
p31ValueStill31 : Hub.monsterLane31Value ≡ 31
p31ValueStill31 = Hub.monsterLane31Is31
