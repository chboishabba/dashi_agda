module DASHI.Physics.CanonicalizationMinimal where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst₂)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

open import Data.Nat using (_≤_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Geometry.StrictContractionComposition as SCC
open import Ultrametric as UMetric
open import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Minimal nontrivial canonicalization on a single Trit

canonTrit : Trit → Trit
canonTrit neg = pos
canonTrit zer = zer
canonTrit pos = pos

canonVec : ∀ {n : Nat} → Vec Trit n → Vec Trit n
canonVec = map canonTrit

------------------------------------------------------------------------
-- Canonicalization on the full state: act only on the coarse core

Cᵣ : ∀ {m k : Nat} → Vec Trit (m + k) → Vec Trit (m + k)
Cᵣ {m} {k} x with TCP.split m k x
... | (c , t) = canonVec c ++ t

------------------------------------------------------------------------
-- Nonexpansiveness (constructive)

Cᵣ-++ :
  ∀ {m k : Nat} (c : Vec Trit m) (t : Vec Trit k) →
  Cᵣ {m} {k} (c ++ t) ≡ canonVec c ++ t
Cᵣ-++ {m} {k} c t
  rewrite TCP.split-++ m k c t = refl

nonexpCᵣ :
  ∀ {m k : Nat} →
  SCC.NonExpansive (FAM.ultrametricVec {n = m + k}) (Cᵣ {m} {k})
nonexpCᵣ {m} {k} =
  record
    { nonexp = nonexp }
  where
    nonexp : ∀ x y → UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) (Cᵣ {m} {k} x) (Cᵣ {m} {k} y)
                       ≤ UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y
    nonexp x y =
      let
        p : x ≡ TCP.coarseOf m k x ++ TCP.tailOf m k x
        p = sym (TCP.merge-split m k x)
        q : y ≡ TCP.coarseOf m k y ++ TCP.tailOf m k y
        q = sym (TCP.merge-split m k y)
        r : Cᵣ {m} {k} x ≡ canonVec (TCP.coarseOf m k x) ++ TCP.tailOf m k x
        r = trans (cong (λ v → Cᵣ {m} {k} v) p)
                  (Cᵣ-++ (TCP.coarseOf m k x) (TCP.tailOf m k x))
        s : Cᵣ {m} {k} y ≡ canonVec (TCP.coarseOf m k y) ++ TCP.tailOf m k y
        s = trans (cong (λ v → Cᵣ {m} {k} v) q)
                  (Cᵣ-++ (TCP.coarseOf m k y) (TCP.tailOf m k y))
        lhs : FAM.dNatFine (canonVec (TCP.coarseOf m k x) ++ TCP.tailOf m k x)
                            (canonVec (TCP.coarseOf m k y) ++ TCP.tailOf m k y)
              ≤ FAM.dNatFine (TCP.coarseOf m k x ++ TCP.tailOf m k x)
                             (TCP.coarseOf m k y ++ TCP.tailOf m k y)
        lhs = FAM.dNatFine-++-map≤
                (TCP.coarseOf m k x) (TCP.coarseOf m k y)
                (TCP.tailOf m k x) (TCP.tailOf m k y)
                canonTrit
        step1 : FAM.dNatFine (Cᵣ {m} {k} x) (Cᵣ {m} {k} y)
                ≤ FAM.dNatFine (TCP.coarseOf m k x ++ TCP.tailOf m k x)
                               (TCP.coarseOf m k y ++ TCP.tailOf m k y)
        step1 =
          subst₂
            (λ a b → FAM.dNatFine a b ≤ FAM.dNatFine (TCP.coarseOf m k x ++ TCP.tailOf m k x)
                                                     (TCP.coarseOf m k y ++ TCP.tailOf m k y))
            (sym r) (sym s) lhs
        step2 : FAM.dNatFine (TCP.coarseOf m k x ++ TCP.tailOf m k x)
                             (TCP.coarseOf m k y ++ TCP.tailOf m k y)
                             ≡ FAM.dNatFine x y
        step2 =
          subst₂
            (λ x' y' → FAM.dNatFine (TCP.coarseOf m k x ++ TCP.tailOf m k x)
                                   (TCP.coarseOf m k y ++ TCP.tailOf m k y)
                                   ≡ FAM.dNatFine x' y')
            (sym p) (sym q) refl
      in
      NatP.≤-trans step1 (NatP.≤-reflexive step2)
