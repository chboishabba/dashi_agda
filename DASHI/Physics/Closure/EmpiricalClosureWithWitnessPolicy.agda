module DASHI.Physics.Closure.EmpiricalClosureWithWitnessPolicy where

open import Level using (Level; zero; suc; _⊔_)
open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.WitnessSetPolicy as WSP

-- Bundle empirical closure seams with an explicit witness-set policy.
record EmpiricalClosureWithWitnessPolicy {ℓ} (W : Set ℓ)
  : Set (suc ℓ ⊔ suc zero) where
  field
    empirical : PCE.PhysicsClosureEmpirical
    policy : WSP.WitnessSetPolicy W

open EmpiricalClosureWithWitnessPolicy public
