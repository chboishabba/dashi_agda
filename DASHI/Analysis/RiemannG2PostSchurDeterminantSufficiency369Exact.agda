module DASHI.Analysis.RiemannG2PostSchurDeterminantSufficiency369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2cPolarizationCompilerExact as G2c
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- POST-SCHUR DETERMINANT SUFFICIENCY / 369 CROSS-POLLINATION
--
-- G2c proves the stronger bilinear statement
--
--   <E x,E y> = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2).
--
-- Therefore the pair of determinant coordinates is an exact sufficient
-- observer for every post-Schur Gram cross term in this abstract interface.
-- Fine three-channel phase/frequency distinctions that preserve both
-- determinant coordinates cannot change that declared consumer.
------------------------------------------------------------------------

PairCell : G2c.PolarizedDeterminantSurface -> Set
PairCell S = G2c.Cell S × G2c.Cell S

determinantPairObserver :
  (S : G2c.PolarizedDeterminantSurface) ->
  PairCell S ->
  G2c.Scalar S × G2c.Scalar S
determinantPairObserver S pair =
  G2c.determinant S (proj₁ pair) , G2c.determinant S (proj₂ pair)

postSchurPairConsumer :
  (S : G2c.PolarizedDeterminantSurface) ->
  PairCell S ->
  G2c.Scalar S
postSchurPairConsumer S pair =
  G2c.dot S (proj₁ pair) (proj₂ pair)

determinantPairFactor :
  (S : G2c.PolarizedDeterminantSurface) ->
  (G2c.Scalar S × G2c.Scalar S) ->
  G2c.Scalar S
determinantPairFactor S pair =
  G2c.divide S
    (G2c.multiply S (proj₁ pair) (proj₂ pair))
    (G2c.wedgeSq S)

postSchurPairFactorsThroughDeterminants :
  (S : G2c.PolarizedDeterminantSurface) ->
  Descent.FactorsThrough
    (determinantPairObserver S)
    (postSchurPairConsumer S)
postSchurPairFactorsThroughDeterminants S =
  Factorized.factorizedRefinement
    (determinantPairFactor S)
    (λ pair ->
      G2c.postSchurDotIsDeterminantProduct S (proj₁ pair) (proj₂ pair))

postSchurDeterminantPairIsConsumerSufficient :
  (S : G2c.PolarizedDeterminantSurface) ->
  Descent.ConsumerSufficient
    (determinantPairObserver S)
    (postSchurPairConsumer S)
postSchurDeterminantPairIsConsumerSufficient S =
  Descent.fibreConstantIsConsumerSufficient
    (Descent.factorsThroughImpliesFibreConstant
      (postSchurPairFactorsThroughDeterminants S))

postSchur369RouteRelation : Relation.RelationKind
postSchur369RouteRelation = Relation.provedSearchObstructionReuse

postSchur369RouteReuse : Relation.ReuseCapability postSchur369RouteRelation
postSchur369RouteReuse = Relation.reuseProvedSearchObstruction

record PostSchurDeterminantSufficiencyBoundary : Set where
  constructor postSchurDeterminantSufficiencyBoundary
  field
    postSchurCrossTermFactorsThroughDeterminantPair : Bool
    postSchurCrossTermFactorsThroughDeterminantPairIsTrue :
      postSchurCrossTermFactorsThroughDeterminantPair ≡ true
    hiddenChannelResidualCanChangeCrossTermWithDeterminantsFixed : Bool
    hiddenChannelResidualCanChangeCrossTermWithDeterminantsFixedIsFalse :
      hiddenChannelResidualCanChangeCrossTermWithDeterminantsFixed ≡ false
    c3DecompositionMayStillHelpProveDeterminantBounds : Bool
    c3DecompositionMayStillHelpProveDeterminantBoundsIsTrue :
      c3DecompositionMayStillHelpProveDeterminantBounds ≡ true
    determinantFactorizationAloneClosesSignedZeroSum : Bool
    determinantFactorizationAloneClosesSignedZeroSumIsFalse :
      determinantFactorizationAloneClosesSignedZeroSum ≡ false
    boundedReading : String

canonicalPostSchurDeterminantSufficiencyBoundary :
  PostSchurDeterminantSufficiencyBoundary
canonicalPostSchurDeterminantSufficiencyBoundary =
  postSchurDeterminantSufficiencyBoundary
    true refl
    false refl
    true refl
    false refl
    "The 369 lesson is now consumer-indexed: do not retain a fine Fourier/residual coordinate merely because it exists. G2c proves that post-Schur Gram cross terms descend through the determinant pair. Any C3 structure must therefore earn relevance by controlling the determinant coordinates themselves or a later consumer not already captured by them."
