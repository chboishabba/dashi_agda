module DASHI.Geometry.RealIsotropyInstanceShiftTailInv where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)
open import Data.Bool using (Bool; true; false; if_then_else_; _xor_)
open import Data.Bool.Properties as BoolP
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst; subst₂)

open import Data.Nat.Properties as NatP
open import Data.Vec using (Vec; _++_)
open import Data.Product using (_,_; proj₁)

open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Algebra.Trit using (Trit; inv)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.TailCollapseInvolution as TCI
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric

cong₂' :
  ∀ {A B C : Set} {x₁ x₂ : A} {y₁ y₂ : B}
  (f : A → B → C) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂' f refl refl = refl

------------------------------------------------------------------------
-- Two-element group acting by tail inversion

boolGroup : Iso.Group Bool
boolGroup =
  record
    { _∙_ = _xor_
    ; e = false
    ; inv = λ a → a
    ; assoc = BoolP.xor-assoc
    ; idL = BoolP.xor-identityˡ
    ; invL = BoolP.xor-same
    }

-- Apply invVec to tail only

tailInv : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k)
tailInv {m} {k} x = TCP.coarseOf m k x ++ RTC.invVec (TCP.tailOf m k x)

tailInv-++ :
  ∀ {m k : Nat} (c : Vec Trit m) (t : Vec Trit k) →
  tailInv {m} {k} (c ++ t) ≡ c ++ RTC.invVec t
tailInv-++ {m} {k} c t
  rewrite TCP.split-++ m k c t = refl

coarseOf-tailInv :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  TCP.coarseOf m k (tailInv {m} {k} x) ≡ TCP.coarseOf m k x
coarseOf-tailInv {m} {k} x with TCP.split m k x
... | (c , t)
  rewrite TCP.split-++ m k c (RTC.invVec t)
  = refl

act : ∀ {m k : Nat} → Bool → RTC.Carrier (m + k) → RTC.Carrier (m + k)
act {m} {k} b x = if b then tailInv {m} {k} x else x

------------------------------------------------------------------------
-- tailInv is an involution

tailInv-invol : ∀ {m k : Nat} (x : RTC.Carrier (m + k)) → tailInv {m} {k} (tailInv {m} {k} x) ≡ x
tailInv-invol {m} {k} x =
  let
    c = TCP.coarseOf m k x
    t = TCP.tailOf m k x
    p : x ≡ c ++ t
    p = sym (TCP.merge-split m k x)
  in
  trans
    (tailInv-++ c (RTC.invVec t))
    (trans
      (cong (λ v → c ++ v) (RTC.invVec-invol t))
      (sym p))

------------------------------------------------------------------------
-- Metric invariance for tailInv

preservesMetric :
  ∀ {m k : Nat} → (g : Bool) → (x y : RTC.Carrier (m + k)) →
  UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) (act {m} {k} g x) (act {m} {k} g y)
    ≡ UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y
preservesMetric {m} {k} false x y = refl
preservesMetric {m} {k} true x y =
  let
    c  = TCP.coarseOf m k x
    t  = TCP.tailOf m k x
    c' = TCP.coarseOf m k y
    t' = TCP.tailOf m k y
    p : x ≡ c ++ t
    p = sym (TCP.merge-split m k x)
    q : y ≡ c' ++ t'
    q = sym (TCP.merge-split m k y)
    le1 : FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t') ≤ FAM.dNatFine (c ++ t) (c' ++ t')
    le1 = FAM.dNatFine-++-map≤-tail c c' t t' inv
    le2 : FAM.dNatFine (c ++ t) (c' ++ t') ≤ FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t')
    le2 =
      let
        le2' : FAM.dNatFine (c ++ RTC.invVec (RTC.invVec t))
                            (c' ++ RTC.invVec (RTC.invVec t'))
               ≤ FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t')
        le2' = FAM.dNatFine-++-map≤-tail c c' (RTC.invVec t) (RTC.invVec t') inv
        r1 : c ++ RTC.invVec (RTC.invVec t) ≡ c ++ t
        r1 = cong (λ v → c ++ v) (RTC.invVec-invol t)
        r2 : c' ++ RTC.invVec (RTC.invVec t') ≡ c' ++ t'
        r2 = cong (λ v → c' ++ v) (RTC.invVec-invol t')
      in
      NatP.≤-trans
        (NatP.≤-reflexive (sym (cong₂' FAM.dNatFine r1 r2)))
        le2'
    le1' : FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t') ≤ FAM.dNatFine x y
    le1' = subst₂ (λ a b → FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t') ≤ FAM.dNatFine a b)
                  (sym p) (sym q) le1
    le2' : FAM.dNatFine x y ≤ FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t')
    le2' = subst₂ (λ a b → FAM.dNatFine a b ≤ FAM.dNatFine (c ++ RTC.invVec t) (c' ++ RTC.invVec t'))
                  (sym p) (sym q) le2
  in
  NatP.≤-antisym le1' le2'

------------------------------------------------------------------------
-- Commutation with the shift stack

commutesWithT :
  ∀ {m k : Nat} → (g : Bool) → (x : RTC.Carrier (m + k)) →
  ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} (act {m} {k} g x)))
    ≡ act {m} {k} g (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
commutesWithT {m} {k} false x = refl
commutesWithT {m} {k} true x =
  let
    c = TCP.coarseOf m k x
    t = TCP.tailOf m k x
    r : act {m} {k} true x ≡ c ++ RTC.invVec t
    r = refl
    stepR : TCP.Rᵣ {m} {k} (c ++ RTC.invVec t) ≡ c ++ TCP.shiftTail (RTC.invVec t)
    stepR = TCP.Rᵣ-++ m k c (RTC.invVec t)
    stepP : TCP.Pᵣ {m} {k} (c ++ TCP.shiftTail (RTC.invVec t)) ≡ c ++ TCP.projTail (TCP.shiftTail (RTC.invVec t))
    stepP = TCP.Pᵣ-++ m k c (TCP.shiftTail (RTC.invVec t))
    stepRP : TCP.Pᵣ {m} {k} (TCP.Rᵣ {m} {k} (c ++ RTC.invVec t)) ≡ c ++ TCP.projTail (TCP.shiftTail (RTC.invVec t))
    stepRP = trans (cong (TCP.Pᵣ {m} {k}) stepR) stepP
    stepC : ROSS.C {m} {k} (c ++ TCP.projTail (TCP.shiftTail (RTC.invVec t)))
            ≡ CM.canonVec c ++ TCP.projTail (TCP.shiftTail (RTC.invVec t))
    stepC = CM.Cᵣ-++ c (TCP.projTail (TCP.shiftTail (RTC.invVec t)))
    t' = TCP.projTail (TCP.shiftTail t)
    p : x ≡ c ++ t
    p = sym (TCP.merge-split m k x)
    stepT : ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)) ≡ CM.canonVec c ++ t'
    stepT =
      let
        r : TCP.Rᵣ {m} {k} x ≡ c ++ TCP.shiftTail t
        r = trans (cong (λ v → TCP.Rᵣ {m} {k} v) p) (TCP.Rᵣ-++ m k c t)
        pr : TCP.Pᵣ {m} {k} (TCP.Rᵣ {m} {k} x) ≡ c ++ TCP.projTail (TCP.shiftTail t)
        pr = trans (cong (λ v → TCP.Pᵣ {m} {k} v) r) (TCP.Pᵣ-++ m k c (TCP.shiftTail t))
      in
      trans
        (cong (λ v → ROSS.C {m} {k} v) pr)
        (CM.Cᵣ-++ c t')
    stepAct : act {m} {k} true (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x))) ≡ CM.canonVec c ++ RTC.invVec t'
    stepAct =
      trans
        (cong (λ v → tailInv {m} {k} v) stepT)
        (tailInv-++ (CM.canonVec c) t')
    stepInv : RTC.invVec (TCP.projTail (TCP.shiftTail t)) ≡ TCP.projTail (TCP.shiftTail (RTC.invVec t))
    stepInv =
      trans
        (TCI.invVec-projTail (TCP.shiftTail t))
        (cong TCP.projTail (TCI.invVec-shiftTail t))
  in
  trans
    (cong (λ v → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} v))) r)
    (trans
      (cong (λ v → ROSS.C {m} {k} v) stepRP)
      (trans
        stepC
        (trans
          (cong (λ v → CM.canonVec c ++ v) (sym stepInv))
          (sym stepAct))))

realIsotropyInstanceTailInv :
  ∀ {m k : Nat} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = m + k})
    (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realIsotropyInstanceTailInv {m} {k} =
  record
    { iso =
        record
          { G = Bool
          ; group = boolGroup
          ; act = act {m} {k}
          ; preservesMetric = preservesMetric {m} {k}
          ; commutesWithT = commutesWithT {m} {k}
          }
    ; coneInvariant = Bool
    }
