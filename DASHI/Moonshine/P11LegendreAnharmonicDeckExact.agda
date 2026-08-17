module DASHI.Moonshine.P11LegendreAnharmonicDeckExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- SOURCE ROLE
--
-- The six changes of full level-2 / Legendre marking form the anharmonic S3
-- acting on lambda by the familiar fractional-linear transformations generated,
-- for example, by
--
--   r(lambda) = 1 - 1/lambda,
--   s(lambda) = lambda/(lambda-1).
--
-- DASHI CONTRIBUTION
--
-- Evaluate those generators on the exact five p=11 supersingular Legendre
-- classes and prove that, under the already-constructed chart to A0,A1,B0,B1,B2,
-- the anharmonic action is literally the same action as the right deck S3
-- descended from the six-frame regular torsor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11SupersingularLegendreLevel2ChartExact as Lambda
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck

------------------------------------------------------------------------
-- Symbolic anharmonic action on the five supersingular lambda classes.
--
-- On the rational roots modulo 11:
--   r: 2 -> 6 -> 10 -> 2,
--   s: 2 fixed, 6 <-> 10.
--
-- On lambda^2-lambda+1=0:
--   r(lambda)=lambda,
--   s(lambda)=1-lambda,
-- so r fixes each root and s swaps the two roots.
------------------------------------------------------------------------

anharmonicR : Lambda.P11SupersingularLambda → Lambda.P11SupersingularLambda
anharmonicR Lambda.lambda2 = Lambda.lambda6
anharmonicR Lambda.lambda6 = Lambda.lambda10
anharmonicR Lambda.lambda10 = Lambda.lambda2
anharmonicR Lambda.lambdaQuadratic0 = Lambda.lambdaQuadratic0
anharmonicR Lambda.lambdaQuadratic1 = Lambda.lambdaQuadratic1

anharmonicS : Lambda.P11SupersingularLambda → Lambda.P11SupersingularLambda
anharmonicS Lambda.lambda2 = Lambda.lambda2
anharmonicS Lambda.lambda6 = Lambda.lambda10
anharmonicS Lambda.lambda10 = Lambda.lambda6
anharmonicS Lambda.lambdaQuadratic0 = Lambda.lambdaQuadratic1
anharmonicS Lambda.lambdaQuadratic1 = Lambda.lambdaQuadratic0

anharmonicR3IsIdentity :
  (x : Lambda.P11SupersingularLambda) →
  anharmonicR (anharmonicR (anharmonicR x)) ≡ x
anharmonicR3IsIdentity Lambda.lambda2 = refl
anharmonicR3IsIdentity Lambda.lambda6 = refl
anharmonicR3IsIdentity Lambda.lambda10 = refl
anharmonicR3IsIdentity Lambda.lambdaQuadratic0 = refl
anharmonicR3IsIdentity Lambda.lambdaQuadratic1 = refl

anharmonicS2IsIdentity :
  (x : Lambda.P11SupersingularLambda) → anharmonicS (anharmonicS x) ≡ x
anharmonicS2IsIdentity Lambda.lambda2 = refl
anharmonicS2IsIdentity Lambda.lambda6 = refl
anharmonicS2IsIdentity Lambda.lambda10 = refl
anharmonicS2IsIdentity Lambda.lambdaQuadratic0 = refl
anharmonicS2IsIdentity Lambda.lambdaQuadratic1 = refl

anharmonicSRSIsRInverse :
  (x : Lambda.P11SupersingularLambda) →
  anharmonicS (anharmonicR (anharmonicS x)) ≡ anharmonicR (anharmonicR x)
anharmonicSRSIsRInverse Lambda.lambda2 = refl
anharmonicSRSIsRInverse Lambda.lambda6 = refl
anharmonicSRSIsRInverse Lambda.lambda10 = refl
anharmonicSRSIsRInverse Lambda.lambdaQuadratic0 = refl
anharmonicSRSIsRInverse Lambda.lambdaQuadratic1 = refl

------------------------------------------------------------------------
-- Exact conjugacy with the frame-torsor deck action on Fine5.
------------------------------------------------------------------------

anharmonicRMatchesDeckR :
  (x : Lambda.P11SupersingularLambda) →
  Lambda.lambdaToFine5 (anharmonicR x)
  ≡ Deck.deckR (Lambda.lambdaToFine5 x)
anharmonicRMatchesDeckR Lambda.lambda2 = refl
anharmonicRMatchesDeckR Lambda.lambda6 = refl
anharmonicRMatchesDeckR Lambda.lambda10 = refl
anharmonicRMatchesDeckR Lambda.lambdaQuadratic0 = refl
anharmonicRMatchesDeckR Lambda.lambdaQuadratic1 = refl

anharmonicSMatchesDeckS :
  (x : Lambda.P11SupersingularLambda) →
  Lambda.lambdaToFine5 (anharmonicS x)
  ≡ Deck.deckS (Lambda.lambdaToFine5 x)
anharmonicSMatchesDeckS Lambda.lambda2 = refl
anharmonicSMatchesDeckS Lambda.lambda6 = refl
anharmonicSMatchesDeckS Lambda.lambda10 = refl
anharmonicSMatchesDeckS Lambda.lambdaQuadratic0 = refl
anharmonicSMatchesDeckS Lambda.lambdaQuadratic1 = refl

------------------------------------------------------------------------
-- The five-state deck action preserves the coarse j projection by construction.
------------------------------------------------------------------------

deckRPreservesJClass :
  (x : Fine.P11Fine5) → Fine.projectFine5 (Deck.deckR x) ≡ Fine.projectFine5 x
deckRPreservesJClass Fine.a0 = refl
deckRPreservesJClass Fine.a1 = refl
deckRPreservesJClass Fine.b0 = refl
deckRPreservesJClass Fine.b1 = refl
deckRPreservesJClass Fine.b2 = refl

deckSPreservesJClass :
  (x : Fine.P11Fine5) → Fine.projectFine5 (Deck.deckS x) ≡ Fine.projectFine5 x
deckSPreservesJClass Fine.a0 = refl
deckSPreservesJClass Fine.a1 = refl
deckSPreservesJClass Fine.b0 = refl
deckSPreservesJClass Fine.b1 = refl
deckSPreservesJClass Fine.b2 = refl

record P11LegendreAnharmonicDeckBoundary : Set where
  field
    anharmonicS3OnSupersingularLambdaConstructed : Bool
    anharmonicS3OnSupersingularLambdaConstructedIsTrue :
      anharmonicS3OnSupersingularLambdaConstructed ≡ true

    anharmonicActionEqualsFrameDeckAction : Bool
    anharmonicActionEqualsFrameDeckActionIsTrue :
      anharmonicActionEqualsFrameDeckAction ≡ true

    deckActionPreservesCoarseJClass : Bool
    deckActionPreservesCoarseJClassIsTrue : deckActionPreservesCoarseJClass ≡ true

    oddHeckeAggregateAlreadyKnownDeckEquivariant : Bool
    oddHeckeAggregateAlreadyKnownDeckEquivariantIsTrue :
      oddHeckeAggregateAlreadyKnownDeckEquivariant ≡ true

    individualHeckeEdgesDerivedFromLambdaModularEquation : Bool
    individualHeckeEdgesDerivedFromLambdaModularEquationIsFalse :
      individualHeckeEdgesDerivedFromLambdaModularEquation ≡ false

canonicalP11LegendreAnharmonicDeckBoundary : P11LegendreAnharmonicDeckBoundary
canonicalP11LegendreAnharmonicDeckBoundary =
  record
    { anharmonicS3OnSupersingularLambdaConstructed = true
    ; anharmonicS3OnSupersingularLambdaConstructedIsTrue = refl
    ; anharmonicActionEqualsFrameDeckAction = true
    ; anharmonicActionEqualsFrameDeckActionIsTrue = refl
    ; deckActionPreservesCoarseJClass = true
    ; deckActionPreservesCoarseJClassIsTrue = refl
    ; oddHeckeAggregateAlreadyKnownDeckEquivariant = true
    ; oddHeckeAggregateAlreadyKnownDeckEquivariantIsTrue = refl
    ; individualHeckeEdgesDerivedFromLambdaModularEquation = false
    ; individualHeckeEdgesDerivedFromLambdaModularEquationIsFalse = refl
    }
