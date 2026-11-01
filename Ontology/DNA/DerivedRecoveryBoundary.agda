module Ontology.DNA.DerivedRecoveryBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; snd)
open import Data.Empty using (⊥)
open import Data.Vec using (Vec; []; _∷_; map)

open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T)
import Ontology.DNA.ChannelCodingSurface as CCS

------------------------------------------------------------------------
-- Derived recovery boundary, plus the current placeholder obstruction.
--
-- The existing `integratedChannelSurface.recoveryBoundary = 3` is a stored
-- field.  This module separates that placeholder from an actually derived
-- one-step recovery law for an explicit outer code, and records why the
-- current default outer code cannot recover a non-empty carrier.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

baseToNat : Base → Nat
baseToNat A = zero
baseToNat C = suc zero
baseToNat G = suc (suc zero)
baseToNat T = suc (suc (suc zero))

natToBase : Nat → Base
natToBase zero = A
natToBase (suc zero) = C
natToBase (suc (suc zero)) = G
natToBase (suc (suc (suc _))) = T

natToBase-baseToNat : (b : Base) → natToBase (baseToNat b) ≡ b
natToBase-baseToNat A = refl
natToBase-baseToNat C = refl
natToBase-baseToNat G = refl
natToBase-baseToNat T = refl

mapNatToBase-baseToNat : ∀ {n} (xs : Vec Base n) →
  map natToBase (map baseToNat xs) ≡ xs
mapNatToBase-baseToNat [] = refl
mapNatToBase-baseToNat (x ∷ xs)
  rewrite natToBase-baseToNat x
        | mapNatToBase-baseToNat xs = refl

derivedOuterCode : CCS.OuterRecoveryCode
derivedOuterCode = record
  { packetize = λ {n} xs → n , map baseToNat xs
  ; recover = λ {k} ns → k , map natToBase ns
  }

derivedRecoverAfterPacketize :
  ∀ {n} (xs : Vec Base n) →
  CCS.OuterRecoveryCode.recover derivedOuterCode
    (snd (CCS.OuterRecoveryCode.packetize derivedOuterCode xs))
  ≡
  (n , xs)
derivedRecoverAfterPacketize xs
  rewrite mapNatToBase-baseToNat xs = refl

record DerivedRecoveryBoundary : Set₁ where
  field
    outerCode : CCS.OuterRecoveryCode
    boundary : Nat
    oneStepBoundary : boundary ≡ suc zero
    oneStepRecovery :
      ∀ {n} (xs : Vec Base n) →
      CCS.OuterRecoveryCode.recover outerCode
        (snd (CCS.OuterRecoveryCode.packetize outerCode xs))
      ≡
      (n , xs)

derivedRecoveryBoundary : DerivedRecoveryBoundary
derivedRecoveryBoundary = record
  { outerCode = derivedOuterCode
  ; boundary = suc zero
  ; oneStepBoundary = refl
  ; oneStepRecovery = derivedRecoverAfterPacketize
  }

defaultOuterCodeCannotRecoverSingletonA :
  CCS.OuterRecoveryCode.recover CCS.defaultOuterCode
    (snd (CCS.OuterRecoveryCode.packetize CCS.defaultOuterCode (A ∷ [])))
  ≢
  (suc zero , A ∷ [])
defaultOuterCodeCannotRecoverSingletonA ()

record CurrentRecoveryBoundaryObstruction : Set where
  field
    storedBoundary : Nat
    defaultNonEmptyRecoveryObstructed :
      CCS.OuterRecoveryCode.recover CCS.defaultOuterCode
        (snd (CCS.OuterRecoveryCode.packetize CCS.defaultOuterCode (A ∷ [])))
      ≢
      (suc zero , A ∷ [])

currentRecoveryBoundaryObstruction : CurrentRecoveryBoundaryObstruction
currentRecoveryBoundaryObstruction = record
  { storedBoundary =
      CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
  ; defaultNonEmptyRecoveryObstructed =
      defaultOuterCodeCannotRecoverSingletonA
  }
