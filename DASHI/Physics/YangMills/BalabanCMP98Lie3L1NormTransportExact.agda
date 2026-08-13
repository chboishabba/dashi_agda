module DASHI.Physics.YangMills.BalabanCMP98Lie3L1NormTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- SOURCE NORMALIZATION / DASHI CORRECTION
--
-- Bałaban's |X| in equations (19), (24)--(38) is the MATRIX OPERATOR NORM,
-- not the repository's three-coordinate l1 norm.  For an su(2) Hermitian
-- generator X = x sigma_1 + y sigma_2 + z sigma_3, each Pauli coordinate is
-- bounded by |X|_op, hence
--
--       |x| + |y| + |z| <= 3 |X|_op.
--
-- Therefore equation (38)'s source estimate
--
--       |Psi(X;Y)|_op <= 24 |X|_op^2
--
-- transports conservatively to
--
--       ||coords Psi||_1 <= 72 ||coords X||_1^2
--
-- provided |X|_op <= ||coords X||_1.  Composing with the existing 4/3
-- Federbush reopening gives 96, not 32, unless a sharper SAME-NORM equation
-- (38) estimate is proved directly in the Lie3 l1 carrier.  The constant 96 is
-- still quadratic and therefore gives the required little-o statement.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

record Lie3Coordinates : Set where
  constructor lie3
  field x y z : ℚ

open Lie3Coordinates public

lie3L1 : Lie3Coordinates → ℚ
lie3L1 value = ∣ x value ∣ + ∣ y value ∣ + ∣ z value ∣

three : ℚ
three = + 3 / 1

seventyTwo : ℚ
seventyTwo = + 72 / 1

ninetySix : ℚ
ninetySix = + 96 / 1

record SourceOperatorNormDominatesCoordinates
    (value : Lie3Coordinates) (sourceNorm : ℚ) : Set where
  field
    sourceNormNonnegative : 0ℚ ≤ sourceNorm
    xBelow : ∣ x value ∣ ≤ sourceNorm
    yBelow : ∣ y value ∣ ≤ sourceNorm
    zBelow : ∣ z value ∣ ≤ sourceNorm

open SourceOperatorNormDominatesCoordinates public

lie3L1BelowThreeSourceNorm :
  ∀ value sourceNorm →
  SourceOperatorNormDominatesCoordinates value sourceNorm →
  lie3L1 value ≤ three * sourceNorm
lie3L1BelowThreeSourceNorm value sourceNorm domination =
  let
    xy = ℚP.+-mono-≤ (xBelow domination) (yBelow domination)
    xyz = ℚP.+-mono-≤ xy (zBelow domination)
  in
  subst
    (λ upper → lie3L1 value ≤ upper)
    (ℚRing.solve-∀ sourceNorm)
    xyz

record SourceOperatorNormBelowLie3L1
    (sourceNorm : ℚ) (value : Lie3Coordinates) : Set where
  field
    sourceNormBelow : sourceNorm ≤ lie3L1 value

open SourceOperatorNormBelowLie3L1 public

record Equation38OperatorToLie3Data
    (input remainder : Lie3Coordinates)
    (inputOperatorNorm remainderOperatorNorm : ℚ) : Set where
  field
    inputSourceDominatesCoordinates :
      SourceOperatorNormDominatesCoordinates input inputOperatorNorm
    remainderSourceDominatesCoordinates :
      SourceOperatorNormDominatesCoordinates remainder remainderOperatorNorm
    inputOperatorBelowLie3 :
      SourceOperatorNormBelowLie3L1 inputOperatorNorm input
    sourceEquation38 :
      Eq38.Equation38QuadraticRemainder
        inputOperatorNorm remainderOperatorNorm

open Equation38OperatorToLie3Data public

squareMonotoneFromNonnegative :
  ∀ left right →
  0ℚ ≤ left → left ≤ right →
  left * left ≤ right * right
squareMonotoneFromNonnegative left right leftNN leftBelow =
  let
    rightNN = ℚP.≤-trans leftNN leftBelow
    first = Norm.scaleNonnegative left leftNN leftBelow
    second = Norm.scaleNonnegative right rightNN leftBelow
  in
  ℚP.≤-trans first second

equation38OperatorBoundImpliesLie3L1Bound72 :
  ∀ input remainder inputOperatorNorm remainderOperatorNorm →
  Equation38OperatorToLie3Data
    input remainder inputOperatorNorm remainderOperatorNorm →
  lie3L1 remainder ≤ seventyTwo * (lie3L1 input * lie3L1 input)
equation38OperatorBoundImpliesLie3L1Bound72
    input remainder inputOperatorNorm remainderOperatorNorm data =
  let
    remainderToSource :
      lie3L1 remainder ≤ three * remainderOperatorNorm
    remainderToSource = lie3L1BelowThreeSourceNorm
      remainder remainderOperatorNorm
      (remainderSourceDominatesCoordinates data)

    sourceQuadratic :
      remainderOperatorNorm
      ≤ Eq38.sourceQuadraticConstant
          * (inputOperatorNorm * inputOperatorNorm)
    sourceQuadratic =
      subst
        (λ upper → remainderOperatorNorm ≤ upper)
        (ℚRing.solve-∀ Eq38.sourceQuadraticConstant inputOperatorNorm)
        (Eq38.sourceQuadraticBound (sourceEquation38 data))

    scaleSource :
      three * remainderOperatorNorm
      ≤ three * (Eq38.sourceQuadraticConstant
          * (inputOperatorNorm * inputOperatorNorm))
    scaleSource = Norm.scaleNonnegative three
      (ℚP.nonNegative⁻¹ three) sourceQuadratic

    inputSquare :
      inputOperatorNorm * inputOperatorNorm
      ≤ lie3L1 input * lie3L1 input
    inputSquare = squareMonotoneFromNonnegative
      inputOperatorNorm (lie3L1 input)
      (sourceNormNonnegative (inputSourceDominatesCoordinates data))
      (sourceNormBelow (inputOperatorBelowLie3 data))

    scaleInputSquare :
      (three * Eq38.sourceQuadraticConstant)
        * (inputOperatorNorm * inputOperatorNorm)
      ≤ (three * Eq38.sourceQuadraticConstant)
        * (lie3L1 input * lie3L1 input)
    scaleInputSquare = Norm.scaleNonnegative
      (three * Eq38.sourceQuadraticConstant)
      (ℚP.nonNegative⁻¹ (three * Eq38.sourceQuadraticConstant))
      inputSquare
  in
  ℚP.≤-trans remainderToSource
    (ℚP.≤-trans
      (subst
        (λ upper → three * remainderOperatorNorm ≤ upper)
        (ℚRing.solve-∀
          three Eq38.sourceQuadraticConstant inputOperatorNorm)
        scaleSource)
      (subst
        (λ lower → lower
          ≤ seventyTwo * (lie3L1 input * lie3L1 input))
        (ℚRing.solve-∀
          three Eq38.sourceQuadraticConstant inputOperatorNorm)
        (subst
          (λ upper →
            (three * Eq38.sourceQuadraticConstant)
              * (inputOperatorNorm * inputOperatorNorm) ≤ upper)
          (ℚRing.solve-∀ (lie3L1 input))
          scaleInputSquare)))

federbushFourThirdsTurns72Into96 :
  ∀ sourceError nonlinearError inputMagnitude →
  nonlinearError ≤ (+ 4 / 3) * sourceError →
  sourceError ≤ seventyTwo * (inputMagnitude * inputMagnitude) →
  nonlinearError ≤ ninetySix * (inputMagnitude * inputMagnitude)
federbushFourThirdsTurns72Into96
    sourceError nonlinearError inputMagnitude reopening sourceBound =
  let
    scaled = Norm.scaleNonnegative (+ 4 / 3)
      (ℚP.nonNegative⁻¹ (+ 4 / 3)) sourceBound
  in
  ℚP.≤-trans reopening
    (subst
      (λ upper →
        (+ 4 / 3) * sourceError ≤ upper)
      (ℚRing.solve-∀ inputMagnitude)
      scaled)

quadratic96ImpliesLittleO :
  ∀ nonlinearError inputMagnitude epsilon →
  0ℚ ≤ inputMagnitude →
  nonlinearError ≤ ninetySix * (inputMagnitude * inputMagnitude) →
  ninetySix * inputMagnitude ≤ epsilon →
  nonlinearError ≤ epsilon * inputMagnitude
quadratic96ImpliesLittleO
    nonlinearError inputMagnitude epsilon inputNN quadratic small =
  let
    scaled = Norm.scaleNonnegative inputMagnitude inputNN small
  in
  ℚP.≤-trans quadratic
    (subst
      (λ upper →
        ninetySix * (inputMagnitude * inputMagnitude) ≤ upper)
      (ℚRing.solve-∀ inputMagnitude epsilon)
      scaled)

cmp98OperatorToLie3L1TransportLevel : ProofLevel
cmp98OperatorToLie3L1TransportLevel = machineChecked

cmp98OperatorBoundConservative72Level : ProofLevel
cmp98OperatorBoundConservative72Level = machineChecked

cmp109FederbushConservative96Level : ProofLevel
cmp109FederbushConservative96Level = machineChecked

cmp109FederbushConservative96LittleOLevel : ProofLevel
cmp109FederbushConservative96LittleOLevel = machineChecked
