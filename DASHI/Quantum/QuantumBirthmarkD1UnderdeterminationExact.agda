{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkD1UnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WHY THE CURRENT BC2 `firstVariation` FIELD CANNOT SUPPLY D1 LAWS BY TYPE
--
-- The production BC2 record stores firstVariation as a bare function.  A bare
-- function carrier admits both derivative-like and non-derivative-like maps.
-- This finite witness exhibits that logical underdetermination directly.
------------------------------------------------------------------------

BareFirstVariation : Set
BareFirstVariation = Nat → Nat

zeroVariation : BareFirstVariation
zeroVariation n = zero

nonzeroVariation : BareFirstVariation
nonzeroVariation zero = zero
nonzeroVariation (suc zero) = zero
nonzeroVariation (suc (suc n)) = suc zero

zeroVariationAtTwo :
  zeroVariation (suc (suc zero)) ≡ zero
zeroVariationAtTwo = refl

nonzeroVariationAtTwo :
  nonzeroVariation (suc (suc zero)) ≡ suc zero
nonzeroVariationAtTwo = refl

nonlinearVariationFailsOnePlusOneAdditivity :
  nonzeroVariation (suc (suc zero))
    ≡ nonzeroVariation (suc zero) → ⊥
nonlinearVariationFailsOnePlusOneAdditivity ()

bareFunctionCarrierAdmitsNonDerivativeLaw : Bool
bareFunctionCarrierAdmitsNonDerivativeLaw = true

bareFunctionDoesNotDetermineLinearityLaws : Bool
bareFunctionDoesNotDetermineLinearityLaws = true

sourceInterfaceStrengtheningStillRequired : Bool
sourceInterfaceStrengtheningStillRequired = true

standardD1AuthorityCanStillBeInstantiatedExternally : Bool
standardD1AuthorityCanStillBeInstantiatedExternally = true
