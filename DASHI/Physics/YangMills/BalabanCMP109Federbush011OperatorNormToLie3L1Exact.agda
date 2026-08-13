module DASHI.Physics.YangMills.BalabanCMP109Federbush011OperatorNormToLie3L1Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Paul Federbush,
-- "A Phase Cell Approach to Yang-Mills Theory. IV. The Choice of Variables",
-- Communications in Mathematical Physics 114 (1988), 317--343.
-- DOI: 10.1007/BF01225039.
--
-- DASHI CONTRIBUTION
--
-- Correctly bridge Bałaban CMP98 equation-(38)'s MATRIX OPERATOR NORM to the
-- literal three-coordinate l1 norm used by the equation-(0.11) reopening.
-- Without a sharper same-norm theorem the safe finite-dimensional transport is
--
--   ||r_source||_1 <= 72 ||X||_1^2,
--
-- and the existing 4/3 Federbush reopening therefore gives
--
--   ||e||_1 <= 96 ||X||_1^2.
--
-- The formerly advertised 32 constant is valid only when a 24-quadratic bound
-- has independently been established in the SAME Lie3 l1 norm.  Differenti-
-- ability needs only a finite quadratic constant, so 96 closes the norm seam
-- without smuggling norm equivalence into the source theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP98Lie3L1NormTransportExact as Transport

toLie3 : (Physical.LieCoordinate3 → ℚ) → Transport.Lie3Coordinates
toLie3 vector = Transport.lie3
  (vector Physical.coordinateX)
  (vector Physical.coordinateY)
  (vector Physical.coordinateZ)

lie3VectorL1Exact : ∀ vector →
  L1.vectorL1 Physical.lieCoordinates3 vector
  ≡ Transport.lie3L1 (toLie3 vector)
lie3VectorL1Exact vector = ℚRing.solve []

record OperatorNormEquation38FederbushData
    (equation : Frechet.FederbushFrechetErrorEquation Physical.LieCoordinate3)
    (input : Physical.LieCoordinate3 → ℚ)
    (inputOperatorNorm remainderOperatorNorm : ℚ) : Set₁ where
  field
    equationUsesLiteralLie3Coordinates :
      Frechet.coordinates equation ≡ Physical.lieCoordinates3

    inputSourceDominatesCoordinates :
      Transport.SourceOperatorNormDominatesCoordinates
        (toLie3 input) inputOperatorNorm

    remainderSourceDominatesCoordinates :
      Transport.SourceOperatorNormDominatesCoordinates
        (toLie3 (Frechet.sourceRemainder equation)) remainderOperatorNorm

    inputOperatorBelowLie3 :
      Transport.SourceOperatorNormBelowLie3L1
        inputOperatorNorm (toLie3 input)

    equation38OperatorRemainder :
      Transport.Equation38OperatorToLie3Data
        (toLie3 input)
        (toLie3 (Frechet.sourceRemainder equation))
        inputOperatorNorm remainderOperatorNorm

open OperatorNormEquation38FederbushData public

literalSourceRemainderQuadratic72 :
  ∀ equation input inputOperatorNorm remainderOperatorNorm →
  OperatorNormEquation38FederbushData
    equation input inputOperatorNorm remainderOperatorNorm →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.sourceRemainder equation)
  ≤ Transport.seventyTwo
      * (L1.vectorL1 Physical.lieCoordinates3 input
        * L1.vectorL1 Physical.lieCoordinates3 input)
literalSourceRemainderQuadratic72
    equation input inputOperatorNorm remainderOperatorNorm data =
  let
    transported = Transport.equation38OperatorBoundImpliesLie3L1Bound72
      (toLie3 input)
      (toLie3 (Frechet.sourceRemainder equation))
      inputOperatorNorm remainderOperatorNorm
      (equation38OperatorRemainder data)

    sourceCoords :
      L1.vectorL1 Physical.lieCoordinates3 (Frechet.sourceRemainder equation)
      ≡ Transport.lie3L1 (toLie3 (Frechet.sourceRemainder equation))
    sourceCoords = lie3VectorL1Exact (Frechet.sourceRemainder equation)

    inputCoords :
      L1.vectorL1 Physical.lieCoordinates3 input
      ≡ Transport.lie3L1 (toLie3 input)
    inputCoords = lie3VectorL1Exact input

    normalized :
      L1.vectorL1 Physical.lieCoordinates3 (Frechet.sourceRemainder equation)
      ≤ Transport.seventyTwo
          * (L1.vectorL1 Physical.lieCoordinates3 input
            * L1.vectorL1 Physical.lieCoordinates3 input)
    normalized =
      subst
        (λ lower → lower
          ≤ Transport.seventyTwo
              * (L1.vectorL1 Physical.lieCoordinates3 input
                * L1.vectorL1 Physical.lieCoordinates3 input))
        (sym sourceCoords)
        (subst
          (λ upper →
            Transport.lie3L1 (toLie3 (Frechet.sourceRemainder equation))
            ≤ Transport.seventyTwo * (upper * upper))
          (sym inputCoords)
          transported)
  in
  subst
    (λ coordinates →
      L1.vectorL1 coordinates (Frechet.sourceRemainder equation)
      ≤ Transport.seventyTwo
          * (L1.vectorL1 Physical.lieCoordinates3 input
            * L1.vectorL1 Physical.lieCoordinates3 input))
    (sym (equationUsesLiteralLie3Coordinates data))
    normalized

literalFederbushErrorQuadratic96 :
  ∀ equation input inputOperatorNorm remainderOperatorNorm →
  OperatorNormEquation38FederbushData
    equation input inputOperatorNorm remainderOperatorNorm →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.error equation)
  ≤ Transport.ninetySix
      * (L1.vectorL1 Physical.lieCoordinates3 input
        * L1.vectorL1 Physical.lieCoordinates3 input)
literalFederbushErrorQuadratic96
    equation input inputOperatorNorm remainderOperatorNorm data =
  let
    source72 = literalSourceRemainderQuadratic72
      equation input inputOperatorNorm remainderOperatorNorm data
    reopened = Frechet.federbushFrechetErrorFourThirdsBound equation
    combined = Transport.federbushFourThirdsTurns72Into96
      (L1.vectorL1 (Frechet.coordinates equation)
        (Frechet.sourceRemainder equation))
      (L1.vectorL1 (Frechet.coordinates equation)
        (Frechet.error equation))
      (L1.vectorL1 Physical.lieCoordinates3 input)
      reopened source72
  in
  combined

cmp109FederbushOperatorNormToLie3L1Level : ProofLevel
cmp109FederbushOperatorNormToLie3L1Level = machineChecked

cmp109FederbushConservativeQuadratic96Level : ProofLevel
cmp109FederbushConservativeQuadratic96Level = machineChecked
