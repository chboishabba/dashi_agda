module DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
-- Uses: Section 5, especially Theorem 1(c), Lemma 5, Remark 1, and the
-- homogeneity system and affine family displayed in equations (42)--(43).
-- Relationship: records the source three-weight exponent method, an exact
-- diagonal rational instance, and the cancellation/separation obligations.
-- The source wavelet threshold 10 is not silently transferred to the DASHI
-- orbit-shell carrier.
--
-- Author: Oleg Kiriukhin.
-- Title: "Orbit-Level Transfer Matrix for the 3D Fourier-Galerkin
-- Navier-Stokes System on the Periodic Torus: Explicit Orbit-Triad
-- Incidence Bounds and Deterministic Row-Sum Estimates".
-- Venue/year: arXiv:2604.12188v1, submitted 14 April 2026.
-- DOI: 10.48550/arXiv.2604.12188.
-- Uses: the two raw row-profile powers in Theorem 6.5.
-- Relationship: proves that row-profile data alone underdetermines the
-- three Grafakos--Torres weight exponents; the two partial-adjoint
-- homogeneity ledgers remain genuinely new inputs.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_<_)
import Data.Integer.Base as Int

record SignedRational : Set where
  constructor rational
  field
    numerator : Int.ℤ
    denominator : Nat

open SignedRational public

positiveRational : Nat → Nat → SignedRational
positiveRational n d = rational (Int.+ n) d

sourceDimension sourceAlpha sourceEpsilonNumerator sourceEpsilonDenominator :
  Nat
sourceDimension = 3
sourceAlpha = 1
sourceEpsilonNumerator = 1
sourceEpsilonDenominator = 4

sourceLeftExponent sourceRightExponent sourceOutputExponent :
  SignedRational
sourceLeftExponent = positiveRational 17 6
sourceRightExponent = positiveRational 17 6
sourceOutputExponent = positiveRational 7 3

sourceCancellationOrder sourceWaveletSeparationThreshold sourceStrictFarGap :
  Nat
sourceCancellationOrder = 3
sourceWaveletSeparationThreshold = 10
sourceStrictFarGap = 11

record GrafakosTorresSourceExponentReceipt : Set where
  constructor source-receipt
  field
    diagonalDimensionIsThree : sourceDimension ≡ 3
    diagonalRegularityIsOne : sourceAlpha ≡ 1
    epsilonNumeratorIsOne : sourceEpsilonNumerator ≡ 1
    epsilonDenominatorIsFour : sourceEpsilonDenominator ≡ 4
    leftExponentNumeratorIsSeventeen :
      numerator sourceLeftExponent ≡ Int.+ 17
    leftExponentDenominatorIsSix :
      denominator sourceLeftExponent ≡ 6
    rightExponentMatchesLeft : sourceRightExponent ≡ sourceLeftExponent
    outputExponentNumeratorIsSeven :
      numerator sourceOutputExponent ≡ Int.+ 7
    outputExponentDenominatorIsThree :
      denominator sourceOutputExponent ≡ 3
    cancellationOrderIsThree : sourceCancellationOrder ≡ 3
    sourceThresholdIsTen : sourceWaveletSeparationThreshold ≡ 10
    firstStrictFarGapIsEleven : sourceStrictFarGap ≡ 11

open GrafakosTorresSourceExponentReceipt public

grafakosTorresSourceExponentReceipt :
  GrafakosTorresSourceExponentReceipt
grafakosTorresSourceExponentReceipt =
  source-receipt refl refl refl refl refl refl refl refl refl refl refl refl

record HomogeneityEquation {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    leftCoefficient rightCoefficient outputCoefficient target : Scalar

open HomogeneityEquation public

record ThreeLegAffineExponentSystem {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    Equation : Set s
    outputEquation firstAdjointEquation secondAdjointEquation : Equation
    leftExponent rightExponent outputExponent epsilon : Scalar

    sourceEquation42Represented : Set s
    affineFamily43Represented : Set s
    outputEquationSatisfied : Set s
    firstAdjointEquationSatisfied : Set s
    secondAdjointEquationSatisfied : Set s
    epsilonStrictlyPositive : Set s
    cancellationOrdersDominateResidualExponents : Set s

open ThreeLegAffineExponentSystem public

record KiriukhinRowOnlyExponentAudit {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    sobolevExponent : Scalar
    slowRowPower fastRowPower : Scalar

    slowPowerIsTwoMinusS : Set s
    fastPowerIsSixMinusThreeS : Set s

    rowDataConstrainsOnlyOutputLeg : Set s
    noFirstPartialAdjointPowerAvailable : Set s
    noSecondPartialAdjointPowerAvailable : Set s
    rowOnlySystemRank : Nat
    threeUnknownCount : Nat
    rowOnlyNullity : Nat
    rankNullityIdentity :
      rowOnlySystemRank + rowOnlyNullity ≡ threeUnknownCount

open KiriukhinRowOnlyExponentAudit public

record KiriukhinTriadicExponentAdapter {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    selectedSobolevExponent : Scalar
    selectedEpsilon : Scalar

    outputRowHomogeneityExtracted : Set s
    firstPartialAdjointHomogeneityExtracted : Set s
    secondPartialAdjointHomogeneityExtracted : Set s
    threeLegAffineSystemSolved : Set s

    sourceWaveletThresholdRecorded : Set s
    repositoryShellOverlapThresholdDerived : Set s
    nearAndTransitionUseUnconditionalMajorant : Set s
    separatedClassesUseCancellationGain : Set s

    allNineOrderingSumsConverge : Set s
    epsilonMarginUniformInCutoff : Set s
    directionWeightPreservesExponentLedger : Set s

open KiriukhinTriadicExponentAdapter public

grafakosTorresExponentSystemRepresented : Bool
grafakosTorresExponentSystemRepresented = true

grafakosTorresExponentSystemRepresentedIsTrue :
  grafakosTorresExponentSystemRepresented ≡ true
grafakosTorresExponentSystemRepresentedIsTrue = refl

kiriukhinRowAloneDeterminesThreeWeights : Bool
kiriukhinRowAloneDeterminesThreeWeights = false

kiriukhinRowAloneDeterminesThreeWeightsIsFalse :
  kiriukhinRowAloneDeterminesThreeWeights ≡ false
kiriukhinRowAloneDeterminesThreeWeightsIsFalse = refl

repositorySeparationThresholdClosed : Bool
repositorySeparationThresholdClosed = false

repositorySeparationThresholdClosedIsFalse :
  repositorySeparationThresholdClosed ≡ false
repositorySeparationThresholdClosedIsFalse = refl
