module DASHI.Physics.TailCollapseMetricProof where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Vec using (Vec; replicate)

open import Ultrametric as UMetric
open import DASHI.Algebra.Trit using (Trit; zer)

open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.TailCollapseProof as TCP

------------------------------------------------------------------------
-- Tail collapse implies distance-to-neutral is zero

tailCollapse-distance0 :
  ∀ (k : Nat) (t : Vec Trit k) →
  FAM.dNatFine (TCP.iterate k TCP.tailStep t) (replicate k zer) ≡ 0
tailCollapse-distance0 k t =
  let
    U : UMetric.Ultrametric (Vec Trit k)
    U = FAM.ultrametricVec {n = k}

    open UMetric.Ultrametric U using (id-zero)
  in
  trans
    (cong (λ x → FAM.dNatFine x (replicate k zer)) (TCP.tailCollapse k t))
    (id-zero (replicate k zer))

tailCollapse-finiteTime :
  ∀ (k : Nat) (t : Vec Trit k) →
  Σ Nat (λ N → FAM.dNatFine (TCP.iterate N TCP.tailStep t) (replicate k zer) ≡ 0)
tailCollapse-finiteTime k t = (k , tailCollapse-distance0 k t)

tailCollapse-fullState-distance0 :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  FAM.dNatFine (TCP.tailOf m k (TCP.iterate k (TCP.Tᵣ {m} {k}) x)) (replicate k zer) ≡ 0
tailCollapse-fullState-distance0 m k x =
  let
    U : UMetric.Ultrametric (Vec Trit k)
    U = FAM.ultrametricVec {n = k}

    open UMetric.Ultrametric U using (id-zero)
  in
  trans
    (cong (λ y → FAM.dNatFine y (replicate k zer)) (TCP.tailOf-after-Tk m k x))
    (id-zero (replicate k zer))
