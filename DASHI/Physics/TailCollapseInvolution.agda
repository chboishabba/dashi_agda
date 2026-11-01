module DASHI.Physics.TailCollapseInvolution where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Data.Vec using (Vec; []; _∷_; _++_; map)
open import Data.Vec.Base using (_∷ʳ_; init)
open import Data.Vec.Properties using (map-++; init-∷ʳ)
open import Data.Product using (_,_)
open import Data.Product using (proj₁; proj₂)

open import DASHI.Algebra.Trit using (Trit; inv; zer)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP

------------------------------------------------------------------------
-- invVec distributes over append

invVec-++ :
  ∀ {m k : Nat} (c : Vec Trit m) (t : Vec Trit k) →
  RTC.invVec (c ++ t) ≡ RTC.invVec c ++ RTC.invVec t
invVec-++ c t = map-++ inv c t

------------------------------------------------------------------------
-- invVec commutes with snoc

invVec-∷ʳ :
  ∀ {k : Nat} (xs : Vec Trit k) (a : Trit) →
  RTC.invVec (xs ∷ʳ a) ≡ RTC.invVec xs ∷ʳ inv a
invVec-∷ʳ {zero} [] a = refl
invVec-∷ʳ {suc k} (x ∷ xs) a =
  cong (inv x ∷_) (invVec-∷ʳ xs a)

------------------------------------------------------------------------
-- invVec commutes with shiftTail

invVec-shiftTail :
  ∀ {k : Nat} (t : Vec Trit k) →
  RTC.invVec (TCP.shiftTail t) ≡ TCP.shiftTail (RTC.invVec t)
invVec-shiftTail {zero} [] = refl
invVec-shiftTail {suc k} (x ∷ xs) =
  trans (invVec-∷ʳ xs zer) refl

------------------------------------------------------------------------
-- invVec commutes with init

invVec-init :
  ∀ {k : Nat} (t : Vec Trit (suc k)) →
  RTC.invVec (init t) ≡ init (RTC.invVec t)
invVec-init {zero} (x ∷ []) = refl
invVec-init {suc k} (x ∷ y ∷ xs) =
  cong (inv x ∷_) (invVec-init (y ∷ xs))

------------------------------------------------------------------------
-- invVec commutes with projTail

invVec-projTail :
  ∀ {k : Nat} (t : Vec Trit k) →
  RTC.invVec (TCP.projTail t) ≡ TCP.projTail (RTC.invVec t)
invVec-projTail {zero} [] = refl
invVec-projTail {suc k} t =
  let
    p : RTC.invVec (init t ∷ʳ zer) ≡ RTC.invVec (init t) ∷ʳ inv zer
    p = invVec-∷ʳ (init t) zer
  in
  trans p (cong (_∷ʳ zer) (invVec-init t))

------------------------------------------------------------------------
-- invVec commutes with Rᵣ and Pᵣ

invVec-Rᵣ :
  ∀ {m k : Nat} (x : Vec Trit (m + k)) →
  RTC.invVec (TCP.Rᵣ {m} {k} x) ≡ TCP.Rᵣ {m} {k} (RTC.invVec x)
invVec-Rᵣ {m} {k} x =
  let
    c = TCP.coarseOf m k x
    t = TCP.tailOf m k x
    p : x ≡ c ++ t
    p = sym (TCP.merge-split m k x)
    q : RTC.invVec x ≡ RTC.invVec c ++ RTC.invVec t
    q = trans (cong RTC.invVec p) (invVec-++ c t)
  in
  trans
    (cong RTC.invVec (trans (cong (λ v → TCP.Rᵣ {m} {k} v) p) (TCP.Rᵣ-++ m k c t)))
    (trans
      (invVec-++ c (TCP.shiftTail t))
      (trans
        (cong (λ v → RTC.invVec c ++ v) (invVec-shiftTail t))
        (sym (trans (cong (λ v → TCP.Rᵣ {m} {k} v) q)
                    (TCP.Rᵣ-++ m k (RTC.invVec c) (RTC.invVec t))))))

invVec-Pᵣ :
  ∀ {m k : Nat} (x : Vec Trit (m + k)) →
  RTC.invVec (TCP.Pᵣ {m} {k} x) ≡ TCP.Pᵣ {m} {k} (RTC.invVec x)
invVec-Pᵣ {m} {k} x =
  let
    c = TCP.coarseOf m k x
    t = TCP.tailOf m k x
    p : x ≡ c ++ t
    p = sym (TCP.merge-split m k x)
    q : RTC.invVec x ≡ RTC.invVec c ++ RTC.invVec t
    q = trans (cong RTC.invVec p) (invVec-++ c t)
  in
  trans
    (cong RTC.invVec (trans (cong (λ v → TCP.Pᵣ {m} {k} v) p) (TCP.Pᵣ-++ m k c t)))
    (trans
      (invVec-++ c (TCP.projTail t))
      (trans
        (cong (λ v → RTC.invVec c ++ v) (invVec-projTail t))
        (sym (trans (cong (λ v → TCP.Pᵣ {m} {k} v) q)
                    (TCP.Pᵣ-++ m k (RTC.invVec c) (RTC.invVec t))))))
