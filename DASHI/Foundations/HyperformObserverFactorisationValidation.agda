module DASHI.Foundations.HyperformObserverFactorisationValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.HyperformObserverFactorisationExact as Factor

data Fine : Set where left right : Fine
data Coarse : Set where same : Coarse

observer : Glue.ObserverWithFibre Fine Coarse
observer = record
  { Glue.observe = λ _ → same
  }

phenomenon : Fine → Bool
phenomenon left = false
phenomenon right = true

distinguishes : phenomenon left ≡ phenomenon right → ⊥
distinguishes ()

witness :
  INF.NonFactorabilityWitness
    (Glue.observe observer)
    phenomenon
witness =
  INF.nonFactorabilityWitness left right refl distinguishes

noBooleanRechartRepairs :
  (rechart : Coarse → Bool) →
  INF.FactorsThrough
    (λ state → rechart (Glue.observe observer state))
    phenomenon →
  ⊥
noBooleanRechartRepairs rechart =
  Factor.rechartCannotRecoverObserverFibreDistinction
    observer rechart witness
