module DASHI.Analysis.HejhalAutomorphyResidual where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MaassFourierCarrier as MFC

------------------------------------------------------------------------
-- Bounds are deliberately an abstract ordered enclosure carrier.  A future
-- interval implementation may instantiate it without changing the residual
-- API below.

postulate
  Bound : Set
  _≤ᵇ_  : Bound → Bound → Set

record MaassResidual : Set where
  field
    samplingResidual      : Bound
    automorphyResidual    : Bound
    laplaceResidual       : Bound
    cuspResidual          : Bound
    truncationResidual    : Bound
    normalisationResidual : Bound
    heckeResidual         : Bound

record ResidualEnclosure (Γ : MFC.ΓMaass)
  (state : MFC.TruncatedFourierState Γ) : Set where
  field
    residual : MaassResidual
    reading  : String

record AutomorphyBound (Γ : MFC.ΓMaass)
  (state : MFC.TruncatedFourierState Γ) : Set where
  field
    enclosure : ResidualEnclosure Γ state
    upperBound : Bound
    automorphyWithinBound :
      MaassResidual.automorphyResidual (ResidualEnclosure.residual enclosure) ≤ᵇ upperBound

