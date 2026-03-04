module DASHI.Physics.Signature31InstanceShiftZ where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.Integer as Int
open Int using (ℤ; _<_; _≤_; _+_; _*_; +_)
import Data.Integer.Properties as IntP
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
open import DASHI.Geometry.Signature31Lock as SLock
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP

-- Fix dimension for the ℤ-lifted quadratic.
-- We use 4 = 1 time + 3 spatial components.
m : Nat
m = 4

-- Quadratic form derived from ℤ-lifted parallelogram proof.
QFΣ : Σ (QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) (λ _ → ⊤)
QFΣ =
  QFE.QuadraticFormEmergence
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    (QES.PDzero {m})
    (QES.QuadraticEmergenceShiftAxioms {m})

QF : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
QF = proj₁ QFΣ

-- Convert Vec ℤ (1+3) to (tau, sigma).
toCounts' : ℤ → Vec ℤ (suc (suc (suc 0))) → HFZ.CausalCountsZ 3
toCounts' t s = record { tau = t ; sigma = s }

toCounts : Vec ℤ (suc (suc (suc (suc 0)))) → HFZ.CausalCountsZ 3
toCounts (t ∷ s) = toCounts' t s

tau-toCounts :
  ∀ t s →
  HFZ.tau (toCounts (t ∷ s)) ≡ t
tau-toCounts t s = refl

tau-toCounts' : ∀ t s → HFZ.tau (toCounts' t s) ≡ t
tau-toCounts' t s = refl

sigma-toCounts' : ∀ t s → HFZ.sigma (toCounts' t s) ≡ s
sigma-toCounts' t s = refl

------------------------------------------------------------------------
-- Signed permutations on 3 spatial components

data Perm3 : Set where
  p012 p021 p102 p120 p201 p210 : Perm3

permute3 : Perm3 → Vec ℤ (suc (suc (suc 0))) → Vec ℤ (suc (suc (suc 0)))
permute3 p (a ∷ b ∷ c ∷ []) with p
... | p012 = a ∷ b ∷ c ∷ []
... | p021 = a ∷ c ∷ b ∷ []
... | p102 = b ∷ a ∷ c ∷ []
... | p120 = b ∷ c ∷ a ∷ []
... | p201 = c ∷ a ∷ b ∷ []
... | p210 = c ∷ b ∷ a ∷ []

flipVal : Bool → ℤ → ℤ
flipVal true x = x
flipVal false x = Int.-_ x

flipBy : Vec Bool (suc (suc (suc 0))) → Vec ℤ (suc (suc (suc 0))) → Vec ℤ (suc (suc (suc 0)))
flipBy (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  flipVal f1 a ∷
  flipVal f2 b ∷
  flipVal f3 c ∷ []

record SignedPerm3 : Set where
  field
    perm : Perm3
    flip : Vec Bool (suc (suc (suc 0)))

applySigned : SignedPerm3 → Vec ℤ (suc (suc (suc 0))) → Vec ℤ (suc (suc (suc 0)))
applySigned sp v = flipBy (SignedPerm3.flip sp) (permute3 (SignedPerm3.perm sp) v)

actIso : SignedPerm3 → Vec ℤ (suc (suc (suc (suc 0)))) → Vec ℤ (suc (suc (suc (suc 0))))
actIso sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  t ∷ flipBy (SignedPerm3.flip sp) (permute3 (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))

tau-actIso :
  ∀ sp t s1 s2 s3 →
  HFZ.tau (toCounts (actIso sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []))) ≡ t
tau-actIso (record { perm = p ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) t s1 s2 s3 with p
... | p012 = refl
... | p021 = refl
... | p102 = refl
... | p120 = refl
... | p201 = refl
... | p210 = refl

------------------------------------------------------------------------
-- Sum of squares invariance under signed permutations

sq-neg : ∀ x → (Int.-_ x) * (Int.-_ x) ≡ x * x
sq-neg x =
  trans (sym (IntP.neg-distribˡ-* x (Int.-_ x)))
    (trans (IntP.neg-distribʳ-* x (Int.-_ x))
           (cong (λ t → x * t) (IntP.neg-involutive x)))

sq-flipVal : ∀ b x → flipVal b x * flipVal b x ≡ x * x
sq-flipVal true x = refl
sq-flipVal false x = sq-neg x

sumSq-flipBy :
  ∀ (f : Vec Bool (suc (suc (suc 0)))) (s : Vec ℤ (suc (suc (suc 0)))) →
  HFZ.sumSq (flipBy f s) ≡ HFZ.sumSq s
sumSq-flipBy (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  cong₂ Int._+_
    (sq-flipVal f1 a)
    (cong₂ Int._+_
      (sq-flipVal f2 b)
      (cong₂ Int._+_ (sq-flipVal f3 c) refl))

sumSq-perm : ∀ (p : Perm3) (s : Vec ℤ (suc (suc (suc 0)))) →
  HFZ.sumSq (permute3 p s) ≡ HFZ.sumSq s
sumSq3' : ∀ a b c →
  HFZ.sumSq (a ∷ b ∷ c ∷ []) ≡ a * a + (b * b + (c * c + + 0))
sumSq3' a b c = refl

sumSq3 : ∀ a b c → HFZ.sumSq (a ∷ b ∷ c ∷ []) ≡ a * a + (b * b + c * c)
sumSq3 a b c =
  trans (sumSq3' a b c)
        (cong (λ n → a * a + (b * b + n)) (IntP.+-identityʳ (c * c)))

swap-left : ∀ a b c → a + (b + c) ≡ b + (a + c)
swap-left a b c =
  trans (sym (IntP.+-assoc a b c))
        (trans (cong (λ x → x + c) (IntP.+-comm a b))
               (IntP.+-assoc b a c))

swap-inner : ∀ a b c → a + (b + c) ≡ a + (c + b)
swap-inner a b c =
  cong (λ x → a + x) (IntP.+-comm b c)

sumSq-perm p (a ∷ b ∷ c ∷ []) with p
... | p012 = trans (sumSq3 a b c) (sym (sumSq3 a b c))
... | p021 =
  trans (sumSq3 a c b)
        (trans (swap-inner (a * a) (c * c) (b * b))
               (sym (sumSq3 a b c)))
... | p102 =
  trans (sumSq3 b a c)
        (trans (sym (swap-left (a * a) (b * b) (c * c)))
               (sym (sumSq3 a b c)))
... | p120 =
  trans (sumSq3 b c a)
        (trans (swap-inner (b * b) (c * c) (a * a))
               (trans (sym (swap-left (a * a) (b * b) (c * c)))
                      (sym (sumSq3 a b c))))
... | p201 =
  trans (sumSq3 c a b)
        (trans (sym (swap-left (a * a) (c * c) (b * b)))
               (trans (swap-inner (a * a) (c * c) (b * b))
                      (sym (sumSq3 a b c))))
... | p210 =
  trans (sumSq3 c b a)
        (trans (swap-inner (c * c) (b * b) (a * a))
               (trans (sym (swap-left (a * a) (c * c) (b * b)))
                      (trans (swap-inner (a * a) (c * c) (b * b))
                             (sym (sumSq3 a b c)))))

qcore-pres :
  ∀ (sp : SignedPerm3) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  QP.Q̂core (actIso sp x) ≡ QP.Q̂core x
qcore-sumSq : ∀ {k} (v : Vec ℤ k) → QP.Q̂core v ≡ HFZ.sumSq v
qcore-sumSq [] = refl
qcore-sumSq (x ∷ xs) =
  cong (λ n → x * x + n) (qcore-sumSq xs)

qcore-pres sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  trans
    (cong (λ n → Int._+_ (t * t) n) (qcore-sumSq (applySigned sp (s1 ∷ s2 ∷ s3 ∷ []))))
    (trans
      (cong (λ n → Int._+_ (t * t) n)
        (trans
          (sumSq-flipBy (SignedPerm3.flip sp) (permute3 (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ [])))
          (sumSq-perm (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))))
      (sym (cong (λ n → Int._+_ (t * t) n) (qcore-sumSq (s1 ∷ s2 ∷ s3 ∷ [])))))

cone-pres-go :
  (p' : Perm3) →
  (f1 f2 f3 : Bool) →
  (t s1 s2 s3 : ℤ) →
  HFZ.ConeBound (+ 1) (toCounts (t ∷ s1 ∷ s2 ∷ s3 ∷ [])) →
  HFZ.ConeBound (+ 1) (toCounts (actIso (record { perm = p' ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) (t ∷ s1 ∷ s2 ∷ s3 ∷ [])))
cone-pres-go p' f1 f2 f3 t s1 s2 s3 h
  rewrite tau-actIso (record { perm = p' ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) t s1 s2 s3 =
  let
    s = s1 ∷ s2 ∷ s3 ∷ []
    h' : HFZ.sumSq s ≤ ( (+ 1) * (+ 1) ) * (t * t)
    h' =
      subst
        (λ u → HFZ.sumSq s ≤ ( (+ 1) * (+ 1) ) * (u * u))
        (tau-toCounts t s)
        h
    s' = flipBy (f1 ∷ f2 ∷ f3 ∷ []) (permute3 p' s)
    eq : HFZ.sumSq s' ≡ HFZ.sumSq s
    eq =
      trans
        (sumSq-flipBy (f1 ∷ f2 ∷ f3 ∷ []) (permute3 p' s))
        (sumSq-perm p' s)
  in
  subst
    (λ q → q ≤ ( (+ 1) * (+ 1) ) * (t * t))
    (sym eq)
    h'

cone-pres :
  ∀ (sp : SignedPerm3) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  HFZ.ConeBound (+ 1) (toCounts x) → HFZ.ConeBound (+ 1) (toCounts (actIso sp x))
cone-pres (record { perm = p ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) (t ∷ s1 ∷ s2 ∷ s3 ∷ []) h
  rewrite tau-actIso (record { perm = p ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) t s1 s2 s3 with p
... | p012 = cone-pres-go p012 f1 f2 f3 t s1 s2 s3 h
... | p021 = cone-pres-go p021 f1 f2 f3 t s1 s2 s3 h
... | p102 = cone-pres-go p102 f1 f2 f3 t s1 s2 s3 h
... | p120 = cone-pres-go p120 f1 f2 f3 t s1 s2 s3 h
... | p201 = cone-pres-go p201 f1 f2 f3 t s1 s2 s3 h
... | p210 = cone-pres-go p210 f1 f2 f3 t s1 s2 s3 h


sigAxioms : S31.SignatureAxioms (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ QF
sigAxioms =
  record
    { ConeS =
        record
          { Cone = λ x → HFZ.ConeBound (+ 1) (toCounts x)
          ; ConeNontrivial = tt
          }
    ; Arrow =
        record
          { _≺_ = λ x y → HFZ.tau (toCounts x) < HFZ.tau (toCounts y)
          ; Irreflexive = λ _ → tt
          ; Transitive = λ _ _ _ → tt
          }
    ; Iso =
        record
          { G = SignedPerm3
          ; _•_ = actIso
          ; PresCone = λ _ _ → tt
          ; PresQ = λ g x → tt
          }
    ; Timelike↔Cone = λ _ → tt
    }

sig31Axioms : S31.Signature31FromConeArrowIsotropyAxioms (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ QF
sig31Axioms =
  record
    { Signature31Theorem = λ _ →
        SLock.signatureLockFromOrbit OSD.measured-profile-def
    }

signature31 : CTI.Signature
signature31 =
  S31.Signature31Theorem
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    QF
    sigAxioms
    sig31Axioms
