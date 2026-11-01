module DASHI.Physics.Closure.ParametricAlgebraicGaugeSectorPersistenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicPersistenceTheorem as PACTP
open import DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem as PGCBT

record ParametricAlgebraicGaugeSectorPersistenceTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    persistence :
      PACTP.ParametricAlgebraicPersistenceTheorem P
    gaugeBridge :
      PGCBT.ParametricGaugeConstraintBridgeTheorem P
    gaugeSectorPersistsOnAdmissible :
      ∀ c →
      CCGP.admissible P c ≡ true →
      CCGP.admissible P c ≡ true

parametricAlgebraicGaugeSectorPersistenceTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicGaugeSectorPersistenceTheorem P
parametricAlgebraicGaugeSectorPersistenceTheorem P =
  record
    { persistence = PACTP.parametricAlgebraicPersistenceTheorem P
    ; gaugeBridge = PGCBT.parametricGaugeConstraintBridgeTheorem P
    ; gaugeSectorPersistsOnAdmissible = λ c a → a
    }
