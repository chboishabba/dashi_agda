module DASHI.Physics.Cone.ArrowSeparatedDeltaConeSplit where

open import Level using (Level; _⊔_; suc)
open import Data.Product using (_×_; _,_; proj₁)

open import DASHI.Physics.Cone.ArrowSeparatedDeltaCone as ASD
open import DASHI.Physics.MaskedOrthogonalSplit as MOS

record SplitCone {ℓs} (Shape : Set ℓs) : Set (suc ℓs) where
  field
    ConeP : Shape → Set ℓs
    ConeQ : Shape → Set ℓs

open SplitCone public

-- Bridge: forward steps ⇒ cone on Δs, and cone on Δs ⇒ cone on split parts.
record ArrowSeparatedConeSplit
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
  (SC : SplitCone (ASD.Shape Split))
  : Set (suc (ℓs ⊔ ℓa ⊔ ℓx ⊔ ℓr)) where
  field
    -- Base arrow-separated cone lemma.
    deltaCone : ASD.ArrowSeparatedDeltaCone Split Δ Fwd Cone Step

    -- Orthogonal split gate for shape deltas.
    splitGate : MOS.MaskedOrthogonalSplit A B QF AR Pr

    -- If the full Δs is in the cone, both split components are cone-compatible.
    coneSplit :
      ∀ {x x'} →
      ASD.ConeStep Split Δ Cone x x' →
      let ds = ASD.ΔShape Δ (proj₁ (ASD.split Split x')) (proj₁ (ASD.split Split x))
      in (SplitCone.ConeP SC (MOS.Projection.P Pr ds)) ×
         (SplitCone.ConeQ SC (MOS.MaskedOrthogonalSplit.Qc splitGate ds))

open ArrowSeparatedConeSplit public

-- Derived: forward step implies split cone predicates.
forwardConeSplit :
  ∀ {ℓs ℓa ℓx ℓr}
  {Split : ASD.ArrowSplit {ℓs} {ℓa} {ℓx}}
  {R : Set ℓr}
  {Δ : ASD.ArrowDelta (ASD.Shape Split) (ASD.Arrow Split)}
  {Fwd : ASD.ForwardPred (ASD.Arrow Split)}
  {Cone : ASD.ConeScreen (ASD.Shape Split)}
  {Step : ASD.State Split → ASD.State Split → Set}
  {A : MOS.Additive (ASD.Shape Split)}
  {B : MOS.Bilinear (ASD.Shape Split) R}
  {QF : MOS.Quadratic (ASD.Shape Split) R}
  {AR : MOS.AdditiveR R}
  {Pr : MOS.Projection (ASD.Shape Split)}
  {SC : SplitCone (ASD.Shape Split)}
  → (kit : ArrowSeparatedConeSplit Split R Δ Fwd Cone Step A B QF AR Pr SC)
  → ∀ {x x'} → Step x x' → ASD.ForwardStep Split Δ Fwd x x'
  → let ds = ASD.ΔShape Δ (proj₁ (ASD.split Split x')) (proj₁ (ASD.split Split x))
        sg = ArrowSeparatedConeSplit.splitGate kit
    in (SplitCone.ConeP SC (MOS.Projection.P Pr ds)) ×
       (SplitCone.ConeQ SC (MOS.MaskedOrthogonalSplit.Qc sg ds))
forwardConeSplit kit st fw =
  ArrowSeparatedConeSplit.coneSplit kit
    (ASD.ArrowSeparatedDeltaCone.forward⇒cone (ArrowSeparatedConeSplit.deltaCone kit) st fw)
