module DASHI.Physics.Closure.CanonicalClosureFibre where

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalClosureShiftScheduleBridge as CCSB
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

------------------------------------------------------------------------
-- Thin closure fibre over the strongest currently bridged canonical quotient.

CanonicalClosureCarrier : Set
CanonicalClosureCarrier =
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage

CanonicalCoarseObservable : Set
CanonicalCoarseObservable =
  CCSB.CanonicalMotifScheduleObservable

π : CanonicalClosureCarrier → CanonicalCoarseObservable
π = CCSB.closureMotifObservable

CanonicalFibre : CanonicalCoarseObservable → Set
CanonicalFibre q = Σ CanonicalClosureCarrier (λ x → π x ≡ q)

carrier : ∀ {q} → CanonicalFibre q → CanonicalClosureCarrier
carrier = fst

sound : ∀ {q} (x : CanonicalFibre q) → π (carrier x) ≡ q
sound = snd

closureDynamicsOnFibre :
  ∀ {q} (x : CanonicalFibre q) →
  CanonicalFibre q
closureDynamicsOnFibre {q} (x , x∈q) =
  CA.canonicalClosureDynamics x
  , trans (sym (CCSB.closureMotifObservablePreserved x)) x∈q
