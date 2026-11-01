module DASHI.Physics.Closure.ObservablePredictionEvidence where

open import Agda.Primitive using (Setω)
open import Level using (_⊔_; suc)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Geometry.DefectCollapse as DC
open import DASHI.Geometry.Signature.Elimination as SE
open import DASHI.MDL.MDLDescentTradeoff as MDL
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.BetaSeamCertificates as BSC
open import DASHI.Physics.Closure.BetaSeamCSVEvidence as BCSV
open import DASHI.Physics.Closure.SignatureLockCSVEvidence as SLCSV

-- Bridge CSV-style evidence bundles into the same observable package surface.
record ObservablePredictionEvidence
  {ℓx ℓs ℓn ℓe}
  {X : Set ℓx}
  {P : E.Preorder {ℓs}}
  {O : MDL.OrderedMonoid {ℓn}}
  {n : Nat}
  {V : Set}
  (ES : E.EnergySpace X P)
  (Pr : CP.Projection X)
  (Ecod : Set ℓe)
  (Parts : MDL.MDLParts X O)
  (Trade : MDL.TradeoffLemma Parts)
  : Setω where
  field
    observables : OPP.ObservablePredictionPackage
    orbitProfile : SE.OrbitProfile V
    signatureEvidence : SLCSV.SignatureRankCSVEvidence {n}
    betaSeamEvidence : BCSV.BetaSeamCSVEvidence ES Pr Ecod Parts Trade

  signatureLock : SE.SignatureLock {n} V
  signatureLock = SLCSV.signatureLockFromRank orbitProfile signatureEvidence

  betaSeams : BSC.BetaSeams ES Pr Ecod Parts Trade
  betaSeams = BCSV.betaSeamsFromEvidence ES Pr Ecod Parts Trade betaSeamEvidence

open ObservablePredictionEvidence public
