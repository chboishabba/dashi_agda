module DASHI.Analysis.RiemannArithmeticUnitarityRigidityBoundary where

------------------------------------------------------------------------
-- PURPOSE
--
-- Typed boundary for the Ramanujan/Hecke version of the dream:
--
--   functional-equation pairing + arithmetic compatibility
--       => unitarity
--       => transverse defect zero.
--
-- This is deliberately an interface theorem.  It does NOT identify zeta zeros
-- with Satake parameters, does NOT assert a new Euler-product representation,
-- and does NOT promote Deligne/Ramanujan bounds to RH.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)

record ArithmeticRigiditySystem : Set₁ where
  field
    State : Set
    functionalEquationPartner : State → State
    transverseDefect : State → Nat
    ArithmeticCompatibility : State → Set
    functionalEquationPairingAvailable : (x : State) → Set
    compatibilityForcesUnitary :
      (x : State) → ArithmeticCompatibility x → transverseDefect x ≡ zero

open ArithmeticRigiditySystem public

rigidityClosesTransverseDefect :
  (r : ArithmeticRigiditySystem) →
  (x : State r) →
  ArithmeticCompatibility r x →
  transverseDefect r x ≡ zero
rigidityClosesTransverseDefect r x compat =
  compatibilityForcesUnitary r x compat

record FunctionalEquationArithmeticCompatibility
  (r : ArithmeticRigiditySystem)
  (x : State r) : Set where
  constructor functionalEquationArithmeticCompatibility
  field
    functionalEquationWitness : functionalEquationPairingAvailable r x
    arithmeticCompatibilityWitness : ArithmeticCompatibility r x

compatibilityPackageForcesUnitary :
  (r : ArithmeticRigiditySystem) →
  (x : State r) →
  FunctionalEquationArithmeticCompatibility r x →
  transverseDefect r x ≡ zero
compatibilityPackageForcesUnitary r x package =
  compatibilityForcesUnitary r x
    (FunctionalEquationArithmeticCompatibility.arithmeticCompatibilityWitness package)

record SatakeAnalogyBoundary : Set₁ where
  field
    LocalParameter : Set
    unitary : LocalParameter → Set
    arithmeticCompatibility : LocalParameter → Set
    compatibilityImpliesUnitary :
      (p : LocalParameter) → arithmeticCompatibility p → unitary p

record ArithmeticUnitarityRigidityBoundary : Set where
  field
    abstractRigidityInterfaceConstructed : Bool
    functionalEquationCompatibilityPackageConstructed : Bool
    abstractCompatibilityToZeroDefectClosed : Bool
    satakeAnalogyKeptTyped : Bool
    zetaZeroSatakeIdentificationProvedHere : Bool
    zetaArithmeticCompatibilityProvedHere : Bool
    rhViaArithmeticRigidityProvedHere : Bool

arithmeticUnitarityRigidityBoundary : ArithmeticUnitarityRigidityBoundary
arithmeticUnitarityRigidityBoundary = record
  { abstractRigidityInterfaceConstructed = true
  ; functionalEquationCompatibilityPackageConstructed = true
  ; abstractCompatibilityToZeroDefectClosed = true
  ; satakeAnalogyKeptTyped = true
  ; zetaZeroSatakeIdentificationProvedHere = false
  ; zetaArithmeticCompatibilityProvedHere = false
  ; rhViaArithmeticRigidityProvedHere = false
  }
