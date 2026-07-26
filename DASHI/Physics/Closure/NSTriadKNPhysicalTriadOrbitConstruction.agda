module DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_; -_)
import Data.Integer.Properties as Int
open import Relation.Binary.PropositionalEquality
  using (cong; sym; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

------------------------------------------------------------------------
-- Exact group laws for Z^3, used to build the three energy-transfer legs.
------------------------------------------------------------------------

modeExt :
  ∀ {a b : Z3.FourierMode} →
  Z3.kx a ≡ Z3.kx b →
  Z3.ky a ≡ Z3.ky b →
  Z3.kz a ≡ Z3.kz b →
  a ≡ b
modeExt {Z3.mode ax ay az} {Z3.mode .ax .ay .az} refl refl refl = refl

addNegateRight :
  ∀ p q → Z3.addMode (Z3.addMode p q) (Z3.negateMode q) ≡ p
addNegateRight (Z3.mode px py pz) (Z3.mode qx qy qz) =
  modeExt
    (cancel px qx)
    (cancel py qy)
    (cancel pz qz)
  where
  cancel : ∀ a b → (a + b) + (- b) ≡ a
  cancel a b =
    begin
      (a + b) + (- b)
    ≡⟨ Int.+-assoc a b (- b) ⟩
      a + (b + (- b))
    ≡⟨ cong (a +_) (Int.+-inverseʳ b) ⟩
      a + (+ 0)
    ≡⟨ Int.+-identityʳ a ⟩
      a
    ∎
    where open ≡-Reasoning

addNegateLeft :
  ∀ p q → Z3.addMode (Z3.addMode p q) (Z3.negateMode p) ≡ q
addNegateLeft (Z3.mode px py pz) (Z3.mode qx qy qz) =
  modeExt
    (cancel px qx)
    (cancel py qy)
    (cancel pz qz)
  where
  cancel : ∀ a b → (a + b) + (- a) ≡ b
  cancel a b =
    begin
      (a + b) + (- a)
    ≡⟨ cong (_+ (- a)) (Int.+-comm a b) ⟩
      (b + a) + (- a)
    ≡⟨ Int.+-assoc b a (- a) ⟩
      b + (a + (- a))
    ≡⟨ cong (b +_) (Int.+-inverseʳ a) ⟩
      b + (+ 0)
    ≡⟨ Int.+-identityʳ b ⟩
      b
    ∎
    where open ≡-Reasoning

pEnergyLeg :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
pEnergyLeg τ =
  Physical.physicalTriad
    (Physical.k τ)
    (Z3.negateMode (Physical.q τ))
    (Physical.p τ)
    proof
  where
  proof :
    Z3.addMode
      (Physical.k τ)
      (Z3.negateMode (Physical.q τ))
    ≡ Physical.p τ
  proof rewrite sym (Physical.resonance τ) =
    addNegateRight (Physical.p τ) (Physical.q τ)

qEnergyLeg :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
qEnergyLeg τ =
  Physical.physicalTriad
    (Physical.k τ)
    (Z3.negateMode (Physical.p τ))
    (Physical.q τ)
    proof
  where
  proof :
    Z3.addMode
      (Physical.k τ)
      (Z3.negateMode (Physical.p τ))
    ≡ Physical.q τ
  proof rewrite sym (Physical.resonance τ) =
    addNegateLeft (Physical.p τ) (Physical.q τ)

pEnergyLegFirstInput :
  ∀ τ → Physical.p (pEnergyLeg τ) ≡ Physical.k τ
pEnergyLegFirstInput τ = refl

pEnergyLegSecondInput :
  ∀ τ →
  Physical.q (pEnergyLeg τ) ≡ Z3.negateMode (Physical.q τ)
pEnergyLegSecondInput τ = refl

pEnergyLegOutput :
  ∀ τ → Physical.k (pEnergyLeg τ) ≡ Physical.p τ
pEnergyLegOutput τ = refl

qEnergyLegFirstInput :
  ∀ τ → Physical.p (qEnergyLeg τ) ≡ Physical.k τ
qEnergyLegFirstInput τ = refl

qEnergyLegSecondInput :
  ∀ τ →
  Physical.q (qEnergyLeg τ) ≡ Z3.negateMode (Physical.p τ)
qEnergyLegSecondInput τ = refl

qEnergyLegOutput :
  ∀ τ → Physical.k (qEnergyLeg τ) ≡ Physical.q τ
qEnergyLegOutput τ = refl

physicalTriadEnergyOrbitConstructed : Bool
physicalTriadEnergyOrbitConstructed = true

physicalTriadEnergyOrbitConstructedIsTrue :
  physicalTriadEnergyOrbitConstructed ≡ true
physicalTriadEnergyOrbitConstructedIsTrue = refl
