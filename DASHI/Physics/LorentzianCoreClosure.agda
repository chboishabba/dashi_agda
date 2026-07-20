module DASHI.Physics.LorentzianCoreClosure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Data.Vec using (Vec)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_; -[1+_])

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedCanonicalizationInvariant as MCI
open import DASHI.Physics.MaskedCone as MC
open import DASHI.Physics.SignatureFromMask as SFM

------------------------------------------------------------------------
-- A fixed m=4 physical core, built as an instance of the parameterized mask
-- algebra. This packages only results already computed/proven in the lower
-- modules; it does not claim dimension uniqueness beyond the orbit theorem.

Core4 : Set
Core4 = Vec Trit 4

Q₄ : Core4 → ℤ
Q₄ = IMQ.Qσ MC.lorentzMask

B₂₄ : Core4 → Core4 → ℤ
B₂₄ = IMQ.B2σ MC.lorentzMask

Dot₄ : Core4 → Core4 → ℤ
Dot₄ = IMQ.dotσ MC.lorentzMask

signature₄ : SFM.signature MC.lorentzMask ≡ (1 , 3)
signature₄ = MC.lorentzSignature

polarization₄ :
  ∀ x y → B₂₄ x y ≡ (+ 2) * Dot₄ x y
polarization₄ = IMQ.B2σ≡2dotσ MC.lorentzMask

canonical-Q₄ :
  ∀ x → Q₄ (CM.canonVec x) ≡ Q₄ x
canonical-Q₄ = MCI.Qσ-canonVec MC.lorentzMask

indefinite₄ : MC.IndefiniteWitness MC.lorentzMask
indefinite₄ = MC.lorentzIndefinite

coordinateOrthogonality₄ :
  MC.Orthogonal MC.lorentzMask MC.timeAxis MC.spaceAxis₁
  × MC.Orthogonal MC.lorentzMask MC.timeAxis MC.spaceAxis₂
  × MC.Orthogonal MC.lorentzMask MC.timeAxis MC.spaceAxis₃
coordinateOrthogonality₄ =
  ( MC.time⊥space₁
  , MC.time⊥space₂
  , MC.time⊥space₃
  )

record LorentzianCoreClosure : Set where
  field
    mask : Vec IMQ.Sign 4
    signature-1+3 : SFM.signature mask ≡ (1 , 3)

    quadratic : Core4 → ℤ
    bilinear₂ : Core4 → Core4 → ℤ
    weightedDot : Core4 → Core4 → ℤ

    polarization :
      ∀ x y → bilinear₂ x y ≡ (+ 2) * weightedDot x y

    canonical-invariance :
      ∀ x → quadratic (CM.canonVec x) ≡ quadratic x

    indefinite : MC.IndefiniteWitness mask

lorentzianCoreClosure : LorentzianCoreClosure
lorentzianCoreClosure =
  record
    { mask = MC.lorentzMask
    ; signature-1+3 = signature₄
    ; quadratic = Q₄
    ; bilinear₂ = B₂₄
    ; weightedDot = Dot₄
    ; polarization = polarization₄
    ; canonical-invariance = canonical-Q₄
    ; indefinite = indefinite₄
    }
