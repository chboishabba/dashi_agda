module DASHI.Physics.Signature31InstanceShiftZ where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (z≤n)
import Data.Integer as Int
open Int using (ℤ; _<_; _≤_; _+_; _*_; +_)
import Data.Integer.Properties as IntP
open import Data.Vec using (Vec; []; _∷_)
import Data.List as List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31OrbitActionAgreement as OAA
open import DASHI.Physics.Signature31ShiftProfileWitness as SPW
open import DASHI.Physics.SignedPerm4 as SP

-- Fix dimension for the ℤ-lifted quadratic.
-- We use 4 = 1 time + 3 spatial components.
m : Nat
m = 4

-- Quadratic form derived from ℤ-lifted parallelogram proof.
QFΣ : Σ (QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) (λ _ → ⊤)
QFΣ = QES.quadraticShiftΣ {m}

QF : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
QF = proj₁ QFΣ

-- Convert Vec ℤ (1+3) to (tau, sigma).
toCounts' : ℤ → Vec ℤ (suc (suc (suc 0))) → HFZ.CausalCountsZ 3
toCounts' t s = record { tau = t ; sigma = s }

toCounts : Vec ℤ (suc (suc (suc (suc 0)))) → HFZ.CausalCountsZ 3
toCounts (t ∷ s) = toCounts' t s

zero4 : Vec ℤ (suc (suc (suc (suc 0))))
zero4 = (+ 0) ∷ (+ 0) ∷ (+ 0) ∷ (+ 0) ∷ []

-- Canonical nonzero shell seed used for cone witnessing in the shift bridge.
-- This is a shell-1 timelike unit axis point, lifted via vecℤ.
shell1SeedTrit : Vec Trit m
shell1SeedTrit = pos ∷ zer ∷ zer ∷ zer ∷ []

shell1SeedIsShell1 : OPCSP.isShell 1 shell1SeedTrit ≡ true
shell1SeedIsShell1 = refl

shell1ConePoint : Vec ℤ m
shell1ConePoint = QP.vecℤ shell1SeedTrit

shell1ConeWitness : HFZ.ConeBound (+ 1) (toCounts shell1ConePoint)
shell1ConeWitness = Int.+≤+ z≤n

coneNontrivialWitness :
  HFZ.ConeBound (+ 1) (toCounts zero4)
coneNontrivialWitness = IntP.≤-refl

tau-toCounts :
  ∀ t s →
  HFZ.tau (toCounts (t ∷ s)) ≡ t
tau-toCounts t s = refl

tau-toCounts' : ∀ t s → HFZ.tau (toCounts' t s) ≡ t
tau-toCounts' t s = refl

sigma-toCounts' : ∀ t s → HFZ.sigma (toCounts' t s) ≡ s
sigma-toCounts' t s = refl

------------------------------------------------------------------------
-- Signed permutations on 3 spatial components (shared definition)

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
    perm : SP.Perm3
    flip : Vec Bool (suc (suc (suc 0)))

applySigned : SignedPerm3 → Vec ℤ (suc (suc (suc 0))) → Vec ℤ (suc (suc (suc 0)))
applySigned sp v = flipBy (SignedPerm3.flip sp) (SP.permute3 (SignedPerm3.perm sp) v)

actIso : SignedPerm3 → Vec ℤ (suc (suc (suc (suc 0)))) → Vec ℤ (suc (suc (suc (suc 0))))
actIso sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  t ∷ flipBy (SignedPerm3.flip sp) (SP.permute3 (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))

flipTritℤ : Bool → ℤ → ℤ
flipTritℤ true x = x
flipTritℤ false x = Int.-_ x

actIso4 : SP.SignedPerm4 → Vec ℤ (suc (suc (suc (suc 0)))) → Vec ℤ (suc (suc (suc (suc 0))))
actIso4 sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  flipTritℤ (SP.SignedPerm4.flipT sp) t ∷
  flipBy (SP.SignedPerm4.flipS sp) (SP.permute3 (SP.SignedPerm4.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))

intOfTrit-flipTrit :
  ∀ b t → QP.intOfTrit (OPCSP.flipTrit b t) ≡ flipVal b (QP.intOfTrit t)
intOfTrit-flipTrit true t = refl
intOfTrit-flipTrit false neg = refl
intOfTrit-flipTrit false zer = refl
intOfTrit-flipTrit false pos = refl

intOfTrit-flipTritT :
  ∀ b t → QP.intOfTrit (OPCSP.flipTrit b t) ≡ flipTritℤ b (QP.intOfTrit t)
intOfTrit-flipTritT true t = refl
intOfTrit-flipTritT false neg = refl
intOfTrit-flipTritT false zer = refl
intOfTrit-flipTritT false pos = refl

vecℤ-flipBy3 :
  ∀ (fs : Vec Bool 3) (s : Vec Trit 3) →
  QP.vecℤ (OPCSP.flipBy3 fs s) ≡ flipBy fs (QP.vecℤ s)
vecℤ-flipBy3 (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  cong₂ _∷_
    (intOfTrit-flipTrit f1 a)
    (cong₂ _∷_
      (intOfTrit-flipTrit f2 b)
      (cong₂ _∷_
        (intOfTrit-flipTrit f3 c)
        refl))

vecℤ-permute3 :
  ∀ (p : SP.Perm3) (s : Vec Trit 3) →
  QP.vecℤ (SP.permute3 p s) ≡ SP.permute3 p (QP.vecℤ s)
vecℤ-permute3 p (a ∷ b ∷ c ∷ []) with p
... | SP.p012 = refl
... | SP.p021 = refl
... | SP.p102 = refl
... | SP.p120 = refl
... | SP.p201 = refl
... | SP.p210 = refl

tau-actIso :
  ∀ sp t s1 s2 s3 →
  HFZ.tau (toCounts (actIso sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []))) ≡ t
tau-actIso (record { perm = p ; flip = f1 ∷ f2 ∷ f3 ∷ [] }) t s1 s2 s3 with p
... | SP.p012 = refl
... | SP.p021 = refl
... | SP.p102 = refl
... | SP.p120 = refl
... | SP.p201 = refl
... | SP.p210 = refl

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

sq-flipTritℤ : ∀ b x → flipTritℤ b x * flipTritℤ b x ≡ x * x
sq-flipTritℤ true x = refl
sq-flipTritℤ false x = sq-neg x

sumSq-flipBy :
  ∀ (f : Vec Bool (suc (suc (suc 0)))) (s : Vec ℤ (suc (suc (suc 0)))) →
  HFZ.sumSq (flipBy f s) ≡ HFZ.sumSq s
sumSq-flipBy (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  cong₂ Int._+_
    (sq-flipVal f1 a)
    (cong₂ Int._+_
      (sq-flipVal f2 b)
      (cong₂ Int._+_ (sq-flipVal f3 c) refl))

sumSq-perm : ∀ (p : SP.Perm3) (s : Vec ℤ (suc (suc (suc 0)))) →
  HFZ.sumSq (SP.permute3 p s) ≡ HFZ.sumSq s
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
... | SP.p012 = trans (sumSq3 a b c) (sym (sumSq3 a b c))
... | SP.p021 =
  trans (sumSq3 a c b)
        (trans (swap-inner (a * a) (c * c) (b * b))
               (sym (sumSq3 a b c)))
... | SP.p102 =
  trans (sumSq3 b a c)
        (trans (sym (swap-left (a * a) (b * b) (c * c)))
               (sym (sumSq3 a b c)))
... | SP.p120 =
  trans (sumSq3 b c a)
        (trans (swap-inner (b * b) (c * c) (a * a))
               (trans (sym (swap-left (a * a) (b * b) (c * c)))
                      (sym (sumSq3 a b c))))
... | SP.p201 =
  trans (sumSq3 c a b)
        (trans (sym (swap-left (a * a) (c * c) (b * b)))
               (trans (swap-inner (a * a) (c * c) (b * b))
                      (sym (sumSq3 a b c))))
... | SP.p210 =
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
          (sumSq-flipBy (SignedPerm3.flip sp) (SP.permute3 (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ [])))
          (sumSq-perm (SignedPerm3.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))))
      (sym (cong (λ n → Int._+_ (t * t) n) (qcore-sumSq (s1 ∷ s2 ∷ s3 ∷ [])))))

sumSq-actIso4 :
  ∀ (sp : SP.SignedPerm4) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  HFZ.sumSq (actIso4 sp x) ≡ HFZ.sumSq x
sumSq-actIso4 sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  cong₂ Int._+_
    (sq-flipTritℤ (SP.SignedPerm4.flipT sp) t)
    (trans
      (sumSq-flipBy (SP.SignedPerm4.flipS sp)
        (SP.permute3 (SP.SignedPerm4.perm sp) (s1 ∷ s2 ∷ s3 ∷ [])))
      (sumSq-perm (SP.SignedPerm4.perm sp) (s1 ∷ s2 ∷ s3 ∷ [])))

qcore-pres4 :
  ∀ (sp : SP.SignedPerm4) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  QP.Q̂core (actIso4 sp x) ≡ QP.Q̂core x
qcore-pres4 sp x =
  trans
    (qcore-sumSq (actIso4 sp x))
    (trans
      (sumSq-actIso4 sp x)
      (sym (qcore-sumSq x)))

actFiniteCompat :
  ∀ (g : SP.SignedPerm4) (x : Vec Trit 4) →
  QP.vecℤ (OAA.actIso4Trit g x) ≡ actIso4 g (QP.vecℤ x)
actFiniteCompat
  (record { perm = p ; flipT = ft ; flipS = fs })
  (t ∷ s1 ∷ s2 ∷ s3 ∷ [])
  =
  cong₂ _∷_
    (intOfTrit-flipTritT ft t)
    (trans
      (vecℤ-flipBy3 fs (SP.permute3 p (s1 ∷ s2 ∷ s3 ∷ [])))
      (cong (flipBy fs) (vecℤ-permute3 p (s1 ∷ s2 ∷ s3 ∷ []))))

shell1-pres :
  ∀ (sp : SP.SignedPerm4) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  QP.Q̂core x ≡ (+ 1) →
  QP.Q̂core (actIso4 sp x) ≡ (+ 1)
shell1-pres sp x h = trans (qcore-pres4 sp x) h

shell2-pres :
  ∀ (sp : SP.SignedPerm4) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  QP.Q̂core x ≡ (+ 2) →
  QP.Q̂core (actIso4 sp x) ≡ (+ 2)
shell2-pres sp x h = trans (qcore-pres4 sp x) h

cone-pres-go :
  (p' : SP.Perm3) →
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
    s' = flipBy (f1 ∷ f2 ∷ f3 ∷ []) (SP.permute3 p' s)
    eq : HFZ.sumSq s' ≡ HFZ.sumSq s
    eq =
      trans
        (sumSq-flipBy (f1 ∷ f2 ∷ f3 ∷ []) (SP.permute3 p' s))
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

cone-pres4 :
  ∀ (sp : SP.SignedPerm4) (x : Vec ℤ (suc (suc (suc (suc 0))))) →
  HFZ.ConeBound (+ 1) (toCounts x) → HFZ.ConeBound (+ 1) (toCounts (actIso4 sp x))
cone-pres4
  (record { perm = p ; flipT = ft ; flipS = fs })
  (t ∷ s1 ∷ s2 ∷ s3 ∷ [])
  h
  rewrite
    sumSq-flipBy fs (SP.permute3 p (s1 ∷ s2 ∷ s3 ∷ []))
  | sumSq-perm p (s1 ∷ s2 ∷ s3 ∷ [])
  | sq-flipTritℤ ft t
  = h


sigAxioms : S31.SignatureAxioms (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ QF
sigAxioms =
  record
    { ConeS =
        record
          { Cone = λ x → HFZ.ConeBound (+ 1) (toCounts x)
          ; ConeNontrivial = let _ = coneNontrivialWitness in tt
          }
    ; Arrow =
        record
          { _≺_ = λ x y → HFZ.tau (toCounts x) < HFZ.tau (toCounts y)
          ; Irreflexive = λ _ → tt
          ; Transitive = λ _ _ _ → tt
          }
    ; Iso =
        record
          { G = SP.SignedPerm4
          ; _•_ = actIso4
          ; PresCone = λ g x → let _ = cone-pres4 g x in tt
          ; PresQ = λ g x → let _ = qcore-pres4 g x in tt
          }
    ; ShellS =
        record
          { Shell1 = λ x → QP.Q̂core x ≡ (+ 1)
          ; Shell2 = λ x → QP.Q̂core x ≡ (+ 2)
          }
    ; MoveS =
        record
          { _↦_ = λ _ _ → ⊤
          }
    ; ShellIso =
        record
          { PresShell1 = λ g x → let _ = shell1-pres g x in tt
          ; PresShell2 = λ g x → let _ = shell2-pres g x in tt
          }
    ; FiniteShell =
        record
          { CarrierPoint = Vec Trit 4
          ; decEq = OPCSP.decEqVec
          ; carrierPoints = OPCSP.allVecTrit 4
          ; embed = QP.vecℤ
          ; shell1Pred = OPCSP.isShell 1
          ; shell2Pred = OPCSP.isShell 2
          }
    ; FiniteIso =
        record
          { GroupPoint = SP.SignedPerm4
          ; groupPoints = OPCSP.allSignedPerm4
          ; actFinite = OAA.actIso4Trit
          ; actCompat = λ g x → let _ = actFiniteCompat g x in tt
          }
    ; Timelike↔Cone = λ _ → tt
    }

sig31Axioms : S31.Signature31FromConeArrowIsotropyAxioms (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ QF
sig31Axioms =
  record
    { Signature31Theorem = λ _ →
        CTI.sig31
    }

signature31 : CTI.Signature
signature31 =
  S31.Signature31Theorem
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    QF
    sigAxioms
    sig31Axioms

-- Shift-instance bridge: cone+arrow+isotropy (in sigAxioms) yields
-- the internally computed orbit profile for sig31.
orientationTagFromArrow :
  S31.SignatureAxioms (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ QF →
  31 ≡ OSD.OrientationTag OSD.sig31
orientationTagFromArrow _ = refl

measuredFromConeArrowShift : OSD.MeasuredProfile ≡ OSD.ProfileOf OSD.sig31
measuredFromConeArrowShift =
  trans
    SPW.measured≡computed
    SPW.computed≡sig31Profile
