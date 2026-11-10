module DASHI.Physics.Motors.Circuit36927InternalTransferConservationExact where

------------------------------------------------------------------------
-- Pure circuit accounting algebra: internal signed transfers cancel.
-- Reuses DASHI's general additive-group walk interface rather than
-- introducing a new current/charge arithmetic foundation.
--
-- It is NOT by itself KCL at each circuit node, nor a power balance,
-- nor evidence of the efficiency of any Resonate369 apparatus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Motors.Resonate369SignedPitchTelescopingExact as Group

module InternalTransfer {A : Set} (G : Group.AngularGroup A) where
  open Group.AngularGroup G

  -- Each internal transfer contributes a negative at its origin and
  -- a positive at its destination in the signed aggregate ledger.
  pairedSignedTransfer : A → A
  pairedSignedTransfer i = neg i ⊕ i

  eachInternalTransferCancels :
    (i : A) → pairedSignedTransfer i ≡ zero
  eachInternalTransferCancels i = leftInverse i

  aggregateInternalTransfers : List A → A
  aggregateInternalTransfers [] = zero
  aggregateInternalTransfers (i ∷ is) =
    pairedSignedTransfer i ⊕ aggregateInternalTransfers is

  -- The total signed contribution from ANY finite family of
  -- strictly internal transfers vanishes, regardless of topology.
  -- The proof uses only the group cancellation axiom and recursion.
  allInternalTransfersCancel :
    (is : List A) → aggregateInternalTransfers is ≡ zero
  allInternalTransfersCancel [] = refl
  allInternalTransfersCancel (i ∷ is)
    rewrite eachInternalTransferCancels i
          | leftUnit (aggregateInternalTransfers is) =
    allInternalTransfersCancel is

-- External ports, ground-return conventions, node-incidence signs,
-- capacitor charge, and physical current conservation are additional
-- source/model obligations. Do not silently assume them here.
