module DASHI.Physics.Closure.NSWholeSpaceCoherentVectorQuadratureCompletionExact where

------------------------------------------------------------------------
-- A / COHERENT VECTOR QUADRATURE COMPLETION
--
-- The finite coherent Gram has already been collapsed exactly:
--
--   G_n ~= ||V_n||^2,
--   V_n = sum_i w_i V_i in C^3.
--
-- Hence convergence of G_n must not be requested as a second independent
-- continuum theorem.  It follows from convergence of the six Bishop-real
-- coordinates of V_n, because multiplication and addition preserve Bishop
-- convergence.
--
-- This owner reduces the coherent same-object limit to the natural Bochner
-- target: convergence of the coherent vector itself.  Pairwise Gram
-- convergence, a free eta_beta coordinate, and an absolute-Gram observer are
-- not used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray
import DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCoherentGramSquareExact as Coherent
import DASHI.Physics.Closure.NSWholeSpaceCoherentGramQuadratureLimitExact as GramLimit

pairNormSquared :
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
pairNormSquared x y =
  BishopReal._+_
    (BishopReal._*_ x x)
    (BishopReal._*_ y y)

pairNormSquaredConverges :
  (xs ys : Nat → BishopReal.ℝ) →
  (x0 y0 : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ xs x0 →
  BishopSequence._ConvergesTo_ ys y0 →
  BishopSequence._ConvergesTo_
    (λ n → pairNormSquared (xs n) (ys n))
    (pairNormSquared x0 y0)
pairNormSquaredConverges xs ys x0 y0 xConv yConv =
  BishopSequence.xₙ+yₙ→x₀+y₀
    ( BishopReal._*_ x0 x0
    , BishopSequence.xₙyₙ→x₀y₀
        (x0 , xConv)
        (x0 , xConv)
    )
    ( BishopReal._*_ y0 y0
    , BishopSequence.xₙyₙ→x₀y₀
        (y0 , yConv)
        (y0 , yConv)
    )

record CoherentVectorQuadratureCompletion : Set₁ where
  constructor coherent-vector-quadrature-completion
  field
    quadratureCells :
      Nat → List Coherent.WeightedComplex3Cell

    limitVector :
      Physical.BishopComplex3

    xRealConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.realPart
            (Physical.cx
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.realPart (Physical.cx limitVector))

    xImagConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.imaginaryPart
            (Physical.cx
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.imaginaryPart (Physical.cx limitVector))

    yRealConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.realPart
            (Physical.cy
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.realPart (Physical.cy limitVector))

    yImagConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.imaginaryPart
            (Physical.cy
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.imaginaryPart (Physical.cy limitVector))

    zRealConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.realPart
            (Physical.cz
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.realPart (Physical.cz limitVector))

    zImagConverges :
      BishopSequence._ConvergesTo_
        (λ n →
          Physical.imaginaryPart
            (Physical.cz
              (Coherent.foldWeighted (quadratureCells n))))
        (Physical.imaginaryPart (Physical.cz limitVector))

open CoherentVectorQuadratureCompletion public

xPairNormConverges :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (λ n →
      Leray.complexNormSquared
        (Physical.cx
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Leray.complexNormSquared (Physical.cx (limitVector Q)))
xPairNormConverges Q =
  pairNormSquaredConverges
    (λ n →
      Physical.realPart
        (Physical.cx
          (Coherent.foldWeighted (quadratureCells Q n))))
    (λ n →
      Physical.imaginaryPart
        (Physical.cx
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Physical.realPart (Physical.cx (limitVector Q)))
    (Physical.imaginaryPart (Physical.cx (limitVector Q)))
    (xRealConverges Q)
    (xImagConverges Q)

yPairNormConverges :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (λ n →
      Leray.complexNormSquared
        (Physical.cy
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Leray.complexNormSquared (Physical.cy (limitVector Q)))
yPairNormConverges Q =
  pairNormSquaredConverges
    (λ n →
      Physical.realPart
        (Physical.cy
          (Coherent.foldWeighted (quadratureCells Q n))))
    (λ n →
      Physical.imaginaryPart
        (Physical.cy
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Physical.realPart (Physical.cy (limitVector Q)))
    (Physical.imaginaryPart (Physical.cy (limitVector Q)))
    (yRealConverges Q)
    (yImagConverges Q)

zPairNormConverges :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (λ n →
      Leray.complexNormSquared
        (Physical.cz
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Leray.complexNormSquared (Physical.cz (limitVector Q)))
zPairNormConverges Q =
  pairNormSquaredConverges
    (λ n →
      Physical.realPart
        (Physical.cz
          (Coherent.foldWeighted (quadratureCells Q n))))
    (λ n →
      Physical.imaginaryPart
        (Physical.cz
          (Coherent.foldWeighted (quadratureCells Q n))))
    (Physical.realPart (Physical.cz (limitVector Q)))
    (Physical.imaginaryPart (Physical.cz (limitVector Q)))
    (zRealConverges Q)
    (zImagConverges Q)

foldNormSquaredConverges :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (λ n →
      Leray.complex3NormSquared
        (Coherent.foldWeighted (quadratureCells Q n)))
    (Leray.complex3NormSquared (limitVector Q))
foldNormSquaredConverges Q =
  BishopSequence.xₙ+yₙ→x₀+y₀
    ( Leray.complexNormSquared (Physical.cx (limitVector Q))
    , xPairNormConverges Q
    )
    ( BishopReal._+_
        (Leray.complexNormSquared (Physical.cy (limitVector Q)))
        (Leray.complexNormSquared (Physical.cz (limitVector Q)))
    , BishopSequence.xₙ+yₙ→x₀+y₀
        ( Leray.complexNormSquared (Physical.cy (limitVector Q))
        , yPairNormConverges Q
        )
        ( Leray.complexNormSquared (Physical.cz (limitVector Q))
        , zPairNormConverges Q
        )
    )

completeGramConvergesFromVectorCoordinates :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (λ n → Coherent.completeGram (quadratureCells Q n))
    (Leray.complex3NormSquared (limitVector Q))
completeGramConvergesFromVectorCoordinates Q =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    {xs =
      λ n →
        Leray.complex3NormSquared
          (Coherent.foldWeighted (quadratureCells Q n))}
    {ys =
      λ n →
        Coherent.completeGram (quadratureCells Q n)}
    (λ n {{_}} →
      BishopP.≃-symm
        (Coherent.completeGramIsFoldNormSquared
          (quadratureCells Q n)))
    ( Leray.complex3NormSquared (limitVector Q)
    , foldNormSquaredConverges Q
    )

asCoherentGramQuadratureApproximation :
  (Q : CoherentVectorQuadratureCompletion) →
  GramLimit.CoherentGramQuadratureApproximation
    (Leray.complex3NormSquared (limitVector Q))
asCoherentGramQuadratureApproximation Q =
  GramLimit.coherent-gram-quadrature-approximation
    (quadratureCells Q)
    (completeGramConvergesFromVectorCoordinates Q)

continuousCoherentVectorNormNonnegative :
  (Q : CoherentVectorQuadratureCompletion) →
  BishopReal.NonNegative
    (Leray.complex3NormSquared (limitVector Q))
continuousCoherentVectorNormNonnegative Q =
  GramLimit.continuousCoherentGramNonnegative
    (asCoherentGramQuadratureApproximation Q)

independentGramQuadratureConvergenceRequired : Bool
independentGramQuadratureConvergenceRequired = false

coherentVectorCoordinateConvergenceRequired : Bool
coherentVectorCoordinateConvergenceRequired = true

pairwisePositiveMajorizationUsed : Bool
pairwisePositiveMajorizationUsed = false

freePairCoordinateIntroduced : Bool
freePairCoordinateIntroduced = false

clayPromotion : Bool
clayPromotion = false

independentGramQuadratureConvergenceRequiredIsFalse :
  independentGramQuadratureConvergenceRequired ≡ false
independentGramQuadratureConvergenceRequiredIsFalse = refl

coherentVectorCoordinateConvergenceRequiredIsTrue :
  coherentVectorCoordinateConvergenceRequired ≡ true
coherentVectorCoordinateConvergenceRequiredIsTrue = refl

pairwisePositiveMajorizationUsedIsFalse :
  pairwisePositiveMajorizationUsed ≡ false
pairwisePositiveMajorizationUsedIsFalse = refl

freePairCoordinateIntroducedIsFalse :
  freePairCoordinateIntroduced ≡ false
freePairCoordinateIntroducedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
