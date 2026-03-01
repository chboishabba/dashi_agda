module DASHI.Physics.Closure.PhysicsClosureEmpiricalWithConeSplit where

open import Level using (Level; _⊔_; suc)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.Cone.ArrowSeparatedDeltaCone as ASD
open import DASHI.Physics.Cone.ArrowSeparatedDeltaConeSplit as ADSplit
open import DASHI.Physics.MaskedOrthogonalSplit as MOS

-- Bundle empirical seams with a cone-split gate.
record PhysicsClosureEmpiricalWithConeSplit
  {ℓs ℓa ℓx ℓr}
  (Split : ASD.ArrowSplit {ℓs} {ℓa} {ℓx})
  (R : Set ℓr)
  (Δ : ASD.ArrowDelta (ASD.Shape Split) (ASD.Arrow Split))
  (Fwd : ASD.ForwardPred (ASD.Arrow Split))
  (Cone : ASD.ConeScreen (ASD.Shape Split))
  (Step : ASD.State Split → ASD.State Split → Set)
  (A : MOS.Additive (ASD.Shape Split))
  (B : MOS.Bilinear (ASD.Shape Split) R)
  (QF : MOS.Quadratic (ASD.Shape Split) R)
  (AR : MOS.AdditiveR R)
  (Pr : MOS.Projection (ASD.Shape Split))
  (SC : ADSplit.SplitCone (ASD.Shape Split))
  : Set (suc (ℓs ⊔ ℓa ⊔ ℓx ⊔ ℓr)) where
  field
    empirical : PCE.PhysicsClosureEmpirical
    coneSplit : ADSplit.ArrowSeparatedConeSplit Split R Δ Fwd Cone Step A B QF AR Pr SC

open PhysicsClosureEmpiricalWithConeSplit public
