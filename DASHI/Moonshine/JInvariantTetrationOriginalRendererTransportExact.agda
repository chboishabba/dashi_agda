module DASHI.Moonshine.JInvariantTetrationOriginalRendererTransportExact where

-- Same-object transport through the ORIGINAL Klein-j renderer.
-- The real source is Render.jValue, not a fresh uninterpreted j function.
-- Still requires a selected Abel-to-renderer point map and equivariance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact as T
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Rep
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein

record RendererAbelWeld
  (S : T.AbelModularExpSystem)
  (R : Render.JPhaseRenderingAlgebra)
  (Action : Rep.J369ModularAction R) : Set₁ where
  field
    selectedTranslation : Rep.Matrix Action
    abelToRendererPoint :
      T.Coordinate S → Klein.Point (Render.klein R)
    sameSourceJ :
      (tau : T.Coordinate S) →
      T.modularJ S tau ≡
      Render.jValue R (abelToRendererPoint tau)
    modularTIntertwines :
      (tau : T.Coordinate S) →
      abelToRendererPoint (T.translate S tau) ≡
      Rep.act Action selectedTranslation (abelToRendererPoint tau)

open RendererAbelWeld public

originalRendererJUnderExponential :
  (S : T.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (Action : Rep.J369ModularAction R) →
  (W : RendererAbelWeld S R Action) →
  (w : T.Point S) →
  Render.jValue R
    (abelToRendererPoint W (T.abel S (T.exponential S w)))
  ≡
  Render.jValue R
    (abelToRendererPoint W (T.abel S w))
originalRendererJUnderExponential S R Action W w =
  trans
    (cong (λ tau → Render.jValue R (abelToRendererPoint W tau))
      (T.abelExponentialLaw S w))
    (trans
      (cong (Render.jValue R) (modularTIntertwines W (T.abel S w)))
      (Rep.jInvariant Action (selectedTranslation W)
        (abelToRendererPoint W (T.abel S w))))

originalRendererColourUnderExponential :
  (S : T.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (Action : Rep.J369ModularAction R) →
  (W : RendererAbelWeld S R Action) →
  (w : T.Point S) →
  Render.jColour R
    (abelToRendererPoint W (T.abel S (T.exponential S w)))
  ≡
  Render.jColour R
    (abelToRendererPoint W (T.abel S w))
originalRendererColourUnderExponential S R Action W w =
  trans
    (cong (λ tau → Render.jColour R (abelToRendererPoint W tau))
      (T.abelExponentialLaw S w))
    (trans
      (cong (Render.jColour R) (modularTIntertwines W (T.abel S w)))
      (Rep.colourInvariant R Action (selectedTranslation W)
        (abelToRendererPoint W (T.abel S w))))

originalRendererObserver27UnderExponential :
  (S : T.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (Action : Rep.J369ModularAction R) →
  (W : RendererAbelWeld S R Action) →
  (w : T.Point S) →
  Render.observer27
    (Render.renderAt R
      (abelToRendererPoint W (T.abel S (T.exponential S w))))
  ≡
  Render.observer27
    (Render.renderAt R
      (abelToRendererPoint W (T.abel S w)))
originalRendererObserver27UnderExponential S R Action W w =
  trans
    (cong
      (λ tau → Render.observer27
        (Render.renderAt R (abelToRendererPoint W tau)))
      (T.abelExponentialLaw S w))
    (trans
      (cong (λ p → Render.observer27 (Render.renderAt R p))
        (modularTIntertwines W (T.abel S w)))
      (Rep.observer27Invariant R Action (selectedTranslation W)
        (abelToRendererPoint W (T.abel S w))))
