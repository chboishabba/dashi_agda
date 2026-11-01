{-# OPTIONS --safe #-}
module DASHI.Ontology.MereologyClassOrderNoConfusionExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge as Lean

------------------------------------------------------------------------
-- ONTOLOGY / MEREOLOGY NO-CONFUSION BRIDGE
--
-- Re-export the pinned Lean theorem contracts that keep part-of separate from
-- class order and instance membership.  This module does not reinterpret the
-- external theorem contract as unrestricted world truth.
------------------------------------------------------------------------

partOfNotSubclassContract :
  Lean.LeanTheoremContract
partOfNotSubclassContract = Lean.contract35

partOfNotInstanceContract :
  Lean.LeanTheoremContract
partOfNotInstanceContract = Lean.contract36

partOfMayBeUsedAsSubclassWithoutBridge : Bool
partOfMayBeUsedAsSubclassWithoutBridge = false

partOfMayBeUsedAsSubclassWithoutBridgeIsFalse :
  partOfMayBeUsedAsSubclassWithoutBridge ≡ false
partOfMayBeUsedAsSubclassWithoutBridgeIsFalse = refl

partOfMayBeUsedAsInstanceWithoutBridge : Bool
partOfMayBeUsedAsInstanceWithoutBridge = false

partOfMayBeUsedAsInstanceWithoutBridgeIsFalse :
  partOfMayBeUsedAsInstanceWithoutBridge ≡ false
partOfMayBeUsedAsInstanceWithoutBridgeIsFalse = refl
