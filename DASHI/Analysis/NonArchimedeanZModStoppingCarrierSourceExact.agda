module DASHI.Analysis.NonArchimedeanZModStoppingCarrierSourceExact where

------------------------------------------------------------------------
-- ZMOD STOPPING-CARRIER SOURCE RECEIPT
--
-- Source repository:
--   sneed-and-feed/adelic-spectral-zeta
--   source head audited: f94b956e6e970c40c8bb9f9c39e9052ad7a5f884
--
-- The source uses the literal finite carrier ZMod (2^n), enumerates it through
-- Finset.univ in theorem-bearing files, and represents every finite T-step
-- binary choice as Fin T -> Bool, again enumerated through Finset.univ.
-- OrbitShadowing.rw_step / rw_path / rw_path_fin own the literal endpoint
-- semantics of those choices.
--
-- This receipt does not claim a theorem the source does not contain:
-- predecessor transitivity and prefix stopping absorption are separate bridges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record ZModStoppingCarrierSourceReceipt : Set where
  constructor zmodStoppingCarrierSourceReceipt
  field
    sourceCommit : String
    zmodTwoPowerCarrierLiteral : Bool
    zmodCarrierFinsetUnivEnumerated : Bool
    finiteBinaryChoiceCarrierLiteral : Bool
    finiteBinaryChoicesFinsetUnivEnumerated : Bool
    rwStepLiteralAffineBranches : Bool
    rwPathFiniteEndpointOwned : Bool
    predecessorTransitivityOwnedInSource : Bool
    prefixStoppingAbsorptionOwnedInSource : Bool

canonicalZModStoppingCarrierSourceReceipt : ZModStoppingCarrierSourceReceipt
canonicalZModStoppingCarrierSourceReceipt =
  zmodStoppingCarrierSourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    true true true true true true false false

zmodFiniteEnumerationSourceOwned :
  ZModStoppingCarrierSourceReceipt.zmodCarrierFinsetUnivEnumerated
    canonicalZModStoppingCarrierSourceReceipt
  ≡ true
zmodFiniteEnumerationSourceOwned = refl

binaryChoiceEnumerationSourceOwned :
  ZModStoppingCarrierSourceReceipt.finiteBinaryChoicesFinsetUnivEnumerated
    canonicalZModStoppingCarrierSourceReceipt
  ≡ true
binaryChoiceEnumerationSourceOwned = refl

rwPathEndpointSemanticsSourceOwned :
  ZModStoppingCarrierSourceReceipt.rwPathFiniteEndpointOwned
    canonicalZModStoppingCarrierSourceReceipt
  ≡ true
rwPathEndpointSemanticsSourceOwned = refl

sourceDoesNotOwnPredecessorTransitivity :
  ZModStoppingCarrierSourceReceipt.predecessorTransitivityOwnedInSource
    canonicalZModStoppingCarrierSourceReceipt
  ≡ false
sourceDoesNotOwnPredecessorTransitivity = refl

sourceDoesNotOwnPrefixStoppingAbsorption :
  ZModStoppingCarrierSourceReceipt.prefixStoppingAbsorptionOwnedInSource
    canonicalZModStoppingCarrierSourceReceipt
  ≡ false
sourceDoesNotOwnPrefixStoppingAbsorption = refl
