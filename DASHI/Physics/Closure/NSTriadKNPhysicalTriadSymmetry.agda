module DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_; -_)
import Data.Integer.Properties as Int
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

modeExt :
  ∀ {a b : Z3.FourierMode} →
  Z3.kx a ≡ Z3.kx b →
  Z3.ky a ≡ Z3.ky b →
  Z3.kz a ≡ Z3.kz b →
  a ≡ b
modeExt {Z3.mode ax ay az} {Z3.mode .ax .ay .az} refl refl refl = refl

addModeCommutative :
  ∀ p q → Z3.addMode p q ≡ Z3.addMode q p
addModeCommutative (Z3.mode px py pz) (Z3.mode qx qy qz) =
  modeExt
    (Int.+-comm px qx)
    (Int.+-comm py qy)
    (Int.+-comm pz qz)

negateModeInvolutive :
  ∀ p → Z3.negateMode (Z3.negateMode p) ≡ p
negateModeInvolutive (Z3.mode px py pz) =
  modeExt
    (Int.neg-involutive px)
    (Int.neg-involutive py)
    (Int.neg-involutive pz)

negateModeAdd :
  ∀ p q →
  Z3.addMode (Z3.negateMode p) (Z3.negateMode q)
  ≡ Z3.negateMode (Z3.addMode p q)
negateModeAdd (Z3.mode px py pz) (Z3.mode qx qy qz) =
  modeExt
    (Int.neg-distrib-+ px qx)
    (Int.neg-distrib-+ py qy)
    (Int.neg-distrib-+ pz qz)

swapTriad :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
swapTriad τ =
  Physical.physicalTriad
    (Physical.q τ)
    (Physical.p τ)
    (Physical.k τ)
    (trans
      (addModeCommutative (Physical.q τ) (Physical.p τ))
      (Physical.resonance τ))

swapTriadP : ∀ τ → Physical.p (swapTriad τ) ≡ Physical.q τ
swapTriadP τ = refl

swapTriadQ : ∀ τ → Physical.q (swapTriad τ) ≡ Physical.p τ
swapTriadQ τ = refl

swapTriadK : ∀ τ → Physical.k (swapTriad τ) ≡ Physical.k τ
swapTriadK τ = refl

swapTriadInvolutive : ∀ τ → swapTriad (swapTriad τ) ≡ τ
swapTriadInvolutive (Physical.physicalTriad p q k resonance) = refl

conjugateTriad :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
conjugateTriad τ =
  Physical.physicalTriad
    (Z3.negateMode (Physical.p τ))
    (Z3.negateMode (Physical.q τ))
    (Z3.negateMode (Physical.k τ))
    (trans
      (negateModeAdd (Physical.p τ) (Physical.q τ))
      (cong Z3.negateMode (Physical.resonance τ)))

conjugateTriadP :
  ∀ τ →
  Physical.p (conjugateTriad τ) ≡ Z3.negateMode (Physical.p τ)
conjugateTriadP τ = refl

conjugateTriadQ :
  ∀ τ →
  Physical.q (conjugateTriad τ) ≡ Z3.negateMode (Physical.q τ)
conjugateTriadQ τ = refl

conjugateTriadK :
  ∀ τ →
  Physical.k (conjugateTriad τ) ≡ Z3.negateMode (Physical.k τ)
conjugateTriadK τ = refl

conjugateTriadInvolutive :
  ∀ τ → conjugateTriad (conjugateTriad τ) ≡ τ
conjugateTriadInvolutive
  (Physical.physicalTriad p q k resonance)
  rewrite negateModeInvolutive p
        | negateModeInvolutive q
        | negateModeInvolutive k = refl

physicalTriadSymmetriesConstructed : Bool
physicalTriadSymmetriesConstructed = true

physicalTriadSymmetriesConstructedIsTrue :
  physicalTriadSymmetriesConstructed ≡ true
physicalTriadSymmetriesConstructedIsTrue = refl
