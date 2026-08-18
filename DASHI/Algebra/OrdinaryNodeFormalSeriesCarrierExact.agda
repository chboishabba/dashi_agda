module DASHI.Algebra.OrdinaryNodeFormalSeriesCarrierExact where

------------------------------------------------------------------------
-- MATHEMATICAL CONTEXT
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
--
-- The standard completed local carrier of an ordinary node is described by
--
--   k[[x,y]]/(xy)  ~=  k[[x]] x_k k[[y]].
--
-- DASHI CONTRIBUTION
--
-- Construct the RIGHT-HAND-SIDE carrier concretely over Z using coefficient
-- streams.  A formal branch series is simply Nat -> Z; residue is coefficient
-- zero.  An ordinary-node series is the proof-relevant pullback of two such
-- streams with equal constant coefficient.
--
-- This gives an actual infinite completed-series carrier and an exact first-jet
-- projection to OrdinaryNodeCotangentJetExact.  Multiplication/convolution is
-- intentionally not reconstructed here, so this file claims carrier-level
-- completed-series structure, not a formal ring isomorphism with
-- Z[[x,y]]/(xy).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)

import DASHI.Algebra.TwoBranchNormalizationPullbackExact as Pullback
import DASHI.Algebra.OrdinaryNodeCotangentJetExact as Jet

FormalSeries : Set
FormalSeries = Nat → ℤ

seriesResidue : FormalSeries → ℤ
seriesResidue series = series 0

ordinaryNodeNormalizationData : Pullback.TwoBranchNormalizationData
ordinaryNodeNormalizationData = record
  { Pullback.LeftBranch = FormalSeries
  ; Pullback.RightBranch = FormalSeries
  ; Pullback.Residue = ℤ
  ; Pullback.leftResidue = seriesResidue
  ; Pullback.rightResidue = seriesResidue
  }

OrdinaryNodeSeries : Set
OrdinaryNodeSeries = Pullback.NodePullback ordinaryNodeNormalizationData

leftSeries : OrdinaryNodeSeries → FormalSeries
leftSeries = Pullback.leftBranch

rightSeries : OrdinaryNodeSeries → FormalSeries
rightSeries = Pullback.rightBranch

nodeConstant : OrdinaryNodeSeries → ℤ
nodeConstant node = leftSeries node 0

nodeConstantFromRight :
  (node : OrdinaryNodeSeries) → nodeConstant node ≡ rightSeries node 0
nodeConstantFromRight node = Pullback.residuesAgree node

------------------------------------------------------------------------
-- Concrete basic streams.
------------------------------------------------------------------------

zeroSeries : FormalSeries
zeroSeries n = + 0

constantSeries : ℤ → FormalSeries
constantSeries c 0 = c
constantSeries c (suc n) = + 0

leftLinearSeries : ℤ → FormalSeries
leftLinearSeries a 0 = + 0
leftLinearSeries a (suc 0) = a
leftLinearSeries a (suc (suc n)) = + 0

rightLinearSeries : ℤ → FormalSeries
rightLinearSeries = leftLinearSeries

constantNodeSeries : ℤ → OrdinaryNodeSeries
constantNodeSeries c =
  Pullback.node-pullback (constantSeries c) (constantSeries c) refl

leftTangentNodeSeries : ℤ → OrdinaryNodeSeries
leftTangentNodeSeries a =
  Pullback.node-pullback (leftLinearSeries a) zeroSeries refl

rightTangentNodeSeries : ℤ → OrdinaryNodeSeries
rightTangentNodeSeries b =
  Pullback.node-pullback zeroSeries (rightLinearSeries b) refl

------------------------------------------------------------------------
-- First-order/cotangent readout.
------------------------------------------------------------------------

firstJet : OrdinaryNodeSeries → Jet.NodeJet
firstJet node =
  Jet.nodeJet
    (leftSeries node 0)
    (leftSeries node 1)
    (rightSeries node 1)

constantNodeFirstJet :
  (c : ℤ) → firstJet (constantNodeSeries c) ≡ Jet.nodeJet c (+ 0) (+ 0)
constantNodeFirstJet c = refl

leftTangentFirstJet :
  (a : ℤ) → firstJet (leftTangentNodeSeries a) ≡ Jet.leftTangent a
leftTangentFirstJet a = refl

rightTangentFirstJet :
  (b : ℤ) → firstJet (rightTangentNodeSeries b) ≡ Jet.rightTangent b
rightTangentFirstJet b = refl

------------------------------------------------------------------------
-- The two normalized branches really retain independent higher coefficients.
-- Equality of the node residue does not collapse the fine branch streams.
------------------------------------------------------------------------

leftCoefficient : Nat → OrdinaryNodeSeries → ℤ
leftCoefficient n node = leftSeries node n

rightCoefficient : Nat → OrdinaryNodeSeries → ℤ
rightCoefficient n node = rightSeries node n

leftTangentCoefficientOne :
  (a : ℤ) → leftCoefficient 1 (leftTangentNodeSeries a) ≡ a
leftTangentCoefficientOne a = refl

leftTangentRightCoefficientOneZero :
  (a : ℤ) → rightCoefficient 1 (leftTangentNodeSeries a) ≡ + 0
leftTangentRightCoefficientOneZero a = refl

rightTangentCoefficientOne :
  (b : ℤ) → rightCoefficient 1 (rightTangentNodeSeries b) ≡ b
rightTangentCoefficientOne b = refl

rightTangentLeftCoefficientOneZero :
  (b : ℤ) → leftCoefficient 1 (rightTangentNodeSeries b) ≡ + 0
rightTangentLeftCoefficientOneZero b = refl

record OrdinaryNodeFormalSeriesCarrierBoundary : Set where
  field
    infiniteBranchSeriesCarrierConstructed : Bool
    equalConstantPullbackConstructed : Bool
    independentBranchCoefficientsRetained : Bool
    firstJetProjectionConstructed : Bool
    seriesMultiplicationConstructed : Bool
    completedRingIsomorphismConstructed : Bool
    actualGeometricLocalRingIdentified : Bool

canonicalOrdinaryNodeFormalSeriesCarrierBoundary :
  OrdinaryNodeFormalSeriesCarrierBoundary
canonicalOrdinaryNodeFormalSeriesCarrierBoundary = record
  { infiniteBranchSeriesCarrierConstructed = true
  ; equalConstantPullbackConstructed = true
  ; independentBranchCoefficientsRetained = true
  ; firstJetProjectionConstructed = true
  ; seriesMultiplicationConstructed = false
  ; completedRingIsomorphismConstructed = false
  ; actualGeometricLocalRingIdentified = false
  }
