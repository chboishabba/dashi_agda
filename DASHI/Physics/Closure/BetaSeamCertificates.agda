module DASHI.Physics.Closure.BetaSeamCertificates where

open import Level using (_⊔_; suc)

open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Geometry.DefectCollapse as DC
open import DASHI.MDL.MDLDescentTradeoff as MDL

-- Abstract seam pack for beta-space certificates (CSV-driven evidence).
-- Parametrize by the concrete energy space, projection, and MDL parts/tradeoff.
record BetaSeams
  {ℓx ℓs ℓn ℓe}
  {X : Set ℓx}
  {P : E.Preorder {ℓs}}
  {O : MDL.OrderedMonoid {ℓn}}
  (ES : E.EnergySpace X P)
  (Pr : CP.Projection X)
  (Ecod : Set ℓe)
  (Parts : MDL.MDLParts X O)
  (Trade : MDL.TradeoffLemma Parts)
  : Set (suc (ℓx ⊔ ℓs ⊔ ℓn ⊔ ℓe)) where
  field
    fejer : CP.FejerMonotone ES Pr
    closest : CP.ClosestPoint ES Pr
    defectCollapse : DC.DefectCollapse X Ecod
    mdlDescent : ∀ x →
      MDL.OrderedMonoid._≤_ O (MDL.MDLParts.MDL Parts (MDL.MDLParts.T Parts x))
                                (MDL.MDLParts.MDL Parts x)

open BetaSeams public
