module DASHI.Cognition.PNF.FreshReplayAuthorityAdmissionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import DASHI.Cognition.PNF.FreshReplayAuthorityAdmissionExact


data TokenRow : Set where
  rootRow childRow : TokenRow

freshRoot = freshAuthorityAdmission rootRow

freshRootNoRead : persistentParityReads freshRoot ≡ zero
freshRootNoRead = refl

freshRootExact : authorityRow freshRoot ≡ rootRow
freshRootExact = refl

replayedChild = replayAuthorityAdmission childRow childRow refl

replayChildHasEvidence :
  persistentParityReads replayedChild ≡ suc zero
replayChildHasEvidence = refl

replayChildExact : authorityRow replayedChild ≡ childRow
replayChildExact = refl

freshOnly : FreshReplayAdmissionPolicy TokenRow TokenRow
freshOnly = compileFreshOnlyPolicy (λ row → row)

freshOnlyRootExact :
  authorityRow (admission freshOnly rootRow) ≡ producerRow freshOnly rootRow
freshOnlyRootExact = finalAuthorityExact freshOnly rootRow
