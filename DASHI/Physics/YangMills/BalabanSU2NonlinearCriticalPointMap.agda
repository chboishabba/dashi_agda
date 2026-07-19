module DASHI.Physics.YangMills.BalabanSU2NonlinearCriticalPointMap where

open import Agda.Builtin.Equality using (_≡_)

record NonlinearCriticalPointMap (Background Coarse Fluctuation : Set) : Set₁ where
  field
    criticalStep : Background → Coarse → Fluctuation → Fluctuation
    criticalEquation : Background → Coarse → Fluctuation → Set
    fixedImpliesCritical :
      ∀ background coarse fluctuation →
      criticalStep background coarse fluctuation ≡ fluctuation →
      criticalEquation background coarse fluctuation

open NonlinearCriticalPointMap public
