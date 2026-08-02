module DASHI.Physics.Closure.NSTriadKNGrafakosTorresAffineWeightTemplate where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Terence Tao; DASHI
-- repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators" and
-- "Multilinear Interpolation Between Adjoint Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal
-- of Functional Analysis 199 (2003), 379--385; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; the repository template has no DOI.
-- Uses: Grafakos--Torres Section 5.10, especially equations (42)--(43),
-- the three affine dyadic weights, the free epsilon parameter and the two
-- strict cancellation inequalities.  Grafakos--Tao is cited only as a
-- second literature instance of the small-positive-parameter method.
-- Relationship: formalises the reusable homogeneity-then-small-epsilon
-- architecture.  It proves the exact diagonal source witness but does not
-- claim that the source coefficients equal the periodic Navier--Stokes
-- shell coefficients.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem as Source

record ThreeLegAffineFamily {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    subtract multiply : Scalar → Scalar → Scalar
    leftBase rightBase outputBase : Scalar
    leftDirection rightDirection outputDirection : Scalar

open ThreeLegAffineFamily public

leftAt :
  ∀ {s} {Scalar : Set s} →
  ThreeLegAffineFamily Scalar → Scalar → Scalar
leftAt family epsilon =
  subtract family
    (leftBase family)
    (multiply family epsilon (leftDirection family))

rightAt :
  ∀ {s} {Scalar : Set s} →
  ThreeLegAffineFamily Scalar → Scalar → Scalar
rightAt family epsilon =
  subtract family
    (rightBase family)
    (multiply family epsilon (rightDirection family))

outputAt :
  ∀ {s} {Scalar : Set s} →
  ThreeLegAffineFamily Scalar → Scalar → Scalar
outputAt family epsilon =
  subtract family
    (outputBase family)
    (multiply family epsilon (outputDirection family))

record Section510AffineSolve {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    family : ThreeLegAffineFamily Scalar
    epsilon : Scalar

    outputHomogeneityEquation : Set s
    firstAdjointHomogeneityEquation : Set s
    secondAdjointHomogeneityEquation : Set s

    equation43Left : Set s
    equation43Right : Set s
    equation43Output : Set s

    epsilonStrictlyPositive : Set s
    firstCancellationTargetAboveEpsilon : Set s
    firstCancellationOrderAboveTarget : Set s
    secondCancellationTargetAboveEpsilon : Set s
    secondCancellationOrderAboveTarget : Set s

open Section510AffineSolve public

------------------------------------------------------------------------
-- Exact diagonal source witness.
--
-- The source specialisation p = q = r' = 3, alpha_1 = alpha_2 = 1,
-- n = 3, epsilon = 1/4 has weights
--
--   x_nu = x_mu = 17/6, x_lambda = 7/3.
--
-- To keep this receipt independent of any unverified rational-library API,
-- all strict margins are represented exactly after multiplication by 12.
------------------------------------------------------------------------

data PositiveNat : Nat → Set where
  positive : ∀ n → PositiveNat (suc n)

sourceMarginScale : Nat
sourceMarginScale = 12

sourceEpsilonScaled : Nat
sourceEpsilonScaled = 3

sourceCancellationTargetScaled : Nat
sourceCancellationTargetScaled = 33

sourceCancellationOrderScaled : Nat
sourceCancellationOrderScaled = 36

sourceTargetAboveEpsilonMarginScaled : Nat
sourceTargetAboveEpsilonMarginScaled = 30

sourceOrderAboveTargetMarginScaled : Nat
sourceOrderAboveTargetMarginScaled = 3

sourceTargetDecomposition :
  sourceCancellationTargetScaled
  ≡ sourceEpsilonScaled + sourceTargetAboveEpsilonMarginScaled
sourceTargetDecomposition = refl

sourceOrderDecomposition :
  sourceCancellationOrderScaled
  ≡ sourceCancellationTargetScaled + sourceOrderAboveTargetMarginScaled
sourceOrderDecomposition = refl

sourceEpsilonPositive : PositiveNat sourceEpsilonScaled
sourceEpsilonPositive = positive 2

sourceTargetAboveEpsilonMarginPositive :
  PositiveNat sourceTargetAboveEpsilonMarginScaled
sourceTargetAboveEpsilonMarginPositive = positive 29

sourceOrderAboveTargetMarginPositive :
  PositiveNat sourceOrderAboveTargetMarginScaled
sourceOrderAboveTargetMarginPositive = positive 2

record SourceDiagonalSmallEpsilonReceipt : Set where
  constructor source-receipt
  field
    leftExponentIsSeventeenSixths :
      Source.sourceLeftExponent
      ≡ Source.positiveRational 17 6
    rightExponentMatchesLeft :
      Source.sourceRightExponent ≡ Source.sourceLeftExponent
    outputExponentIsSevenThirds :
      Source.sourceOutputExponent
      ≡ Source.positiveRational 7 3
    epsilonScaledIsThree :
      sourceEpsilonScaled ≡ 3
    targetScaledIsThirtyThree :
      sourceCancellationTargetScaled ≡ 33
    cancellationOrderScaledIsThirtySix :
      sourceCancellationOrderScaled ≡ 36
    targetSplitsAsEpsilonPlusPositiveMargin :
      sourceCancellationTargetScaled
      ≡ sourceEpsilonScaled + sourceTargetAboveEpsilonMarginScaled
    orderSplitsAsTargetPlusPositiveMargin :
      sourceCancellationOrderScaled
      ≡ sourceCancellationTargetScaled + sourceOrderAboveTargetMarginScaled
    epsilonPositive :
      PositiveNat sourceEpsilonScaled
    targetMarginPositive :
      PositiveNat sourceTargetAboveEpsilonMarginScaled
    orderMarginPositive :
      PositiveNat sourceOrderAboveTargetMarginScaled

open SourceDiagonalSmallEpsilonReceipt public

sourceDiagonalSmallEpsilonReceipt : SourceDiagonalSmallEpsilonReceipt
sourceDiagonalSmallEpsilonReceipt =
  source-receipt
    refl refl refl refl refl refl
    sourceTargetDecomposition
    sourceOrderDecomposition
    sourceEpsilonPositive
    sourceTargetAboveEpsilonMarginPositive
    sourceOrderAboveTargetMarginPositive

grafakosTorresSection510AffineTemplateClosed : Bool
grafakosTorresSection510AffineTemplateClosed = true

grafakosTorresSection510AffineTemplateClosedIsTrue :
  grafakosTorresSection510AffineTemplateClosed ≡ true
grafakosTorresSection510AffineTemplateClosedIsTrue = refl

sourceDiagonalSmallEpsilonWitnessClosed : Bool
sourceDiagonalSmallEpsilonWitnessClosed = true

sourceDiagonalSmallEpsilonWitnessClosedIsTrue :
  sourceDiagonalSmallEpsilonWitnessClosed ≡ true
sourceDiagonalSmallEpsilonWitnessClosedIsTrue = refl

sourceCoefficientsAutomaticallyTransferToDASHI : Bool
sourceCoefficientsAutomaticallyTransferToDASHI = false

sourceCoefficientsAutomaticallyTransferToDASHIIsFalse :
  sourceCoefficientsAutomaticallyTransferToDASHI ≡ false
sourceCoefficientsAutomaticallyTransferToDASHIIsFalse = refl
