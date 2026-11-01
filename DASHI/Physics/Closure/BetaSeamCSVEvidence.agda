module DASHI.Physics.Closure.BetaSeamCSVEvidence where

open import Level using (Level; _⊔_; suc)
open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Geometry.DefectCollapse as DC
open import DASHI.MDL.MDLDescentTradeoff as MDL
open import DASHI.Physics.Closure.BetaSeamCertificates as BSC

-- Evidence bundle meant to be populated from CSV-derived proofs.
record BetaSeamCSVEvidence
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

open BetaSeamCSVEvidence public

betaSeamsFromEvidence :
  ∀ {ℓx ℓs ℓn ℓe}
  {X : Set ℓx}
  {P : E.Preorder {ℓs}}
  {O : MDL.OrderedMonoid {ℓn}}
  (ES : E.EnergySpace X P)
  (Pr : CP.Projection X)
  (Ecod : Set ℓe)
  (Parts : MDL.MDLParts X O)
  (Trade : MDL.TradeoffLemma Parts)
  (Ev : BetaSeamCSVEvidence ES Pr Ecod Parts Trade)
  → BSC.BetaSeams ES Pr Ecod Parts Trade
betaSeamsFromEvidence ES Pr Ecod Parts Trade Ev =
  record
    { fejer = BetaSeamCSVEvidence.fejer Ev
    ; closest = BetaSeamCSVEvidence.closest Ev
    ; defectCollapse = BetaSeamCSVEvidence.defectCollapse Ev
    ; mdlDescent = BetaSeamCSVEvidence.mdlDescent Ev
    }
