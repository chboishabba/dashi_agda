module DASHI.Physics.Closure.NSWholeSpaceCoherentGramQuadratureLimitExact where

------------------------------------------------------------------------
-- A / COHERENT GRAM QUADRATURE -> CONTINUOUS POSITIVITY
--
-- The finite coherent owner proves on the literal Bishop C^3 carrier
--
--   completeGram(cells)
--      ~= || sum_i w_i V_i ||^2 >= 0.
--
-- This file performs the continuum step without reverting to pairwise
-- majorisation.  If literal finite coherent quadratures converge to the
-- selected continuous coherent Gram, Bishop order closure under sequential
-- limits gives nonnegativity of that continuous Gram.
--
-- The only analytic input left is same-object convergence of the coherent
-- quadrature.  No free eta_beta coordinate and no |Gram| observer appear.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Physics.Closure.NSWholeSpaceBishopCauchyPSDLimitExact as Limit
import DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCoherentGramSquareExact as Coherent

record CoherentGramQuadratureApproximation
    (continuousCoherentGram : BishopReal.ℝ) : Set₁ where
  constructor coherent-gram-quadrature-approximation
  field
    quadratureCells :
      Nat → List Coherent.WeightedComplex3Cell

    coherentQuadratureConverges :
      BishopSequence._ConvergesTo_
        (λ index →
          Coherent.completeGram
            (quadratureCells index))
        continuousCoherentGram

open CoherentGramQuadratureApproximation public

finiteCoherentQuadratureNonnegative :
  ∀ {continuousCoherentGram} →
  (A : CoherentGramQuadratureApproximation continuousCoherentGram) →
  (index : Nat) →
  BishopReal.NonNegative
    (Coherent.completeGram (quadratureCells A index))
finiteCoherentQuadratureNonnegative A index =
  Coherent.completeGramNonnegative
    (quadratureCells A index)

continuousCoherentGramNonnegative :
  ∀ {continuousCoherentGram} →
  CoherentGramQuadratureApproximation continuousCoherentGram →
  BishopReal.NonNegative continuousCoherentGram
continuousCoherentGramNonnegative {continuousCoherentGram} A =
  Limit.nonnegativeSequenceLimit
    (λ index →
      Coherent.completeGram
        (quadratureCells A index))
    (finiteCoherentQuadratureNonnegative A)
    continuousCoherentGram
    (coherentQuadratureConverges A)

coherentFiniteToContinuousPositivityClosed : Bool
coherentFiniteToContinuousPositivityClosed = true

pairwisePositiveMajorizationUsed : Bool
pairwisePositiveMajorizationUsed = false

freePairCoordinateIntroduced : Bool
freePairCoordinateIntroduced = false

absoluteGramObserverUsed : Bool
absoluteGramObserverUsed = false

remainingInputIsCoherentQuadratureConvergence : Bool
remainingInputIsCoherentQuadratureConvergence = true

clayPromotion : Bool
clayPromotion = false

coherentFiniteToContinuousPositivityClosedIsTrue :
  coherentFiniteToContinuousPositivityClosed ≡ true
coherentFiniteToContinuousPositivityClosedIsTrue = refl

pairwisePositiveMajorizationUsedIsFalse :
  pairwisePositiveMajorizationUsed ≡ false
pairwisePositiveMajorizationUsedIsFalse = refl

freePairCoordinateIntroducedIsFalse :
  freePairCoordinateIntroduced ≡ false
freePairCoordinateIntroducedIsFalse = refl

absoluteGramObserverUsedIsFalse :
  absoluteGramObserverUsed ≡ false
absoluteGramObserverUsedIsFalse = refl

remainingInputIsCoherentQuadratureConvergenceIsTrue :
  remainingInputIsCoherentQuadratureConvergence ≡ true
remainingInputIsCoherentQuadratureConvergenceIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
