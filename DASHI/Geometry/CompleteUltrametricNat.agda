module DASHI.Geometry.CompleteUltrametricNat where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (_≤_; _<_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Ultrametric as UMetric
open import DASHI.Geometry.CompleteUltrametric as CU

private
  one : Nat
  one = suc zero

  one< : 0 < one
  one< = s≤s z≤n

-- Any ℕ-valued ultrametric space is complete under the Cauchy definition.
completeNatUltrametric :
  ∀ {S : Set} (U : UMetric.Ultrametric S) → CU.Complete U
completeNatUltrametric U =
  let open UMetric.Ultrametric U in
  record
    { limit = λ c → CU.Cauchy.seq c (proj₁ (CU.Cauchy.cauchy c one one<))
    ; converges = λ c ε ε>0 →
        let
          N = proj₁ (CU.Cauchy.cauchy c one one<)
          cauchy1 = proj₂ (CU.Cauchy.cauchy c one one<)
          one≤ε : one ≤ ε
          one≤ε = ε>0
        in
        N , λ n N≤n →
          let
            dNn = cauchy1 N n NatP.≤-refl N≤n
            dNn' = subst (λ t → t < one)
                          (UMetric.Ultrametric.symmetric U (CU.Cauchy.seq c N) (CU.Cauchy.seq c n))
                          dNn
          in
          NatP.<-≤-trans dNn' one≤ε
    }
