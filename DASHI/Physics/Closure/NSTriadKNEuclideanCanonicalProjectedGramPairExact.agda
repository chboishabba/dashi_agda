module DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedGramPairExact where

------------------------------------------------------------------------
-- A / CANONICAL SAME-OUTPUT PROJECTED GRAM PAIR
--
-- The periodic R290 observable is an off-diagonal Hermitian Gram between TWO
-- physical cells at one common output.  A single projected-cell norm is only
-- the diagonal special case and must not silently replace that object.
--
-- This owner constructs the literal continuous analogue:
--
--   alpha = (xi, eta_a, xi-eta_a)
--   beta  = (xi, eta_b, xi-eta_b)
--
-- at one common time and one punctured output xi.  Each projected cell is the
-- canonical divergence-form/Leray interaction.  The pair scalar is exactly
--
--   2 Re < P_xi N_alpha , P_xi N_beta >,
--
-- i.e. the existing Euclidean projectedGram object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedInteractionExact as CanonicalCell
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedGramQuadraticMajorantExact as Projected
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramQuadraticMajorantExact as Raw

record CanonicalProjectedGramPair
    {S : Canonical.CanonicalNSSemantics}
    (trajectory : Physical.EuclideanFourierTrajectory S)
    (point : Heat.PuncturedEuclideanFrequency) : Set₁ where
  constructor canonical-projected-gram-pair
  field
    alpha beta : Euclidean.EuclideanInteraction

    alphaOutputExact :
      Euclidean.xi alpha ≡ Heat.frequency point

    betaOutputExact :
      Euclidean.xi beta ≡ Heat.frequency point

    time : Canonical.Time

open CanonicalProjectedGramPair public

alphaCell :
  ∀ {S trajectory point} →
  CanonicalProjectedGramPair
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) point →
  Physical.EuclideanProjectedInteraction trajectory
alphaCell {trajectory = trajectory} {point = point} pair =
  CanonicalCell.canonicalProjectedInteraction
    trajectory point
    (alpha pair)
    (alphaOutputExact pair)
    (time pair)

betaCell :
  ∀ {S trajectory point} →
  CanonicalProjectedGramPair
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) point →
  Physical.EuclideanProjectedInteraction trajectory
betaCell {trajectory = trajectory} {point = point} pair =
  CanonicalCell.canonicalProjectedInteraction
    trajectory point
    (beta pair)
    (betaOutputExact pair)
    (time pair)

pairGram :
  ∀ {S trajectory point} →
  CanonicalProjectedGramPair
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) point →
  BishopReal.ℝ
pairGram {point = point} pair =
  Projected.projectedGram
    point
    (Physical.uEta (alphaCell pair))
    (Physical.uZeta (alphaCell pair))
    (Physical.uEta (betaCell pair))
    (Physical.uZeta (betaCell pair))

pairMajorant :
  ∀ {S trajectory point} →
  CanonicalProjectedGramPair
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) point →
  BishopReal.ℝ
pairMajorant pair =
  Raw.rawGramStateMajorant
    (Physical.uEta (alphaCell pair))
    (Physical.uZeta (alphaCell pair))
    (Physical.uEta (betaCell pair))
    (Physical.uZeta (betaCell pair))

pairGramOutputQBound :
  ∀ {S trajectory point} →
  (pair :
    CanonicalProjectedGramPair
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) point) →
  BishopReal._≤_
    (pairGram pair)
    (BishopReal._*_
      (Heat.frequencyNormSquared (Heat.frequency point))
      (pairMajorant pair))
pairGramOutputQBound {point = point} pair =
  Projected.projectedGramQuadraticMajorant
    point
    (Physical.uEta (alphaCell pair))
    (Physical.uZeta (alphaCell pair))
    (Physical.uEta (betaCell pair))
    (Physical.uZeta (betaCell pair))

pairMajorantNonnegative :
  ∀ {S trajectory point} →
  (pair :
    CanonicalProjectedGramPair
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) point) →
  BishopReal.NonNegative (pairMajorant pair)
pairMajorantNonnegative pair =
  Raw.rawGramStateMajorantNonnegative
    (Physical.uEta (alphaCell pair))
    (Physical.uZeta (alphaCell pair))
    (Physical.uEta (betaCell pair))
    (Physical.uZeta (betaCell pair))

canonicalPairUsesTwoSameOutputCells : Bool
canonicalPairUsesTwoSameOutputCells = true

pairGramIsOffDiagonalCapable : Bool
pairGramIsOffDiagonalCapable = true

pairGramQMajorantClosed : Bool
pairGramQMajorantClosed = true

clayPromotion : Bool
clayPromotion = false

canonicalPairUsesTwoSameOutputCellsIsTrue :
  canonicalPairUsesTwoSameOutputCells ≡ true
canonicalPairUsesTwoSameOutputCellsIsTrue = refl

pairGramIsOffDiagonalCapableIsTrue :
  pairGramIsOffDiagonalCapable ≡ true
pairGramIsOffDiagonalCapableIsTrue = refl

pairGramQMajorantClosedIsTrue :
  pairGramQMajorantClosed ≡ true
pairGramQMajorantClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
