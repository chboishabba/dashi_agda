module DASHI.Physics.YangMills.BalabanCMP109LiteralFederbushCancellationDictionaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Close the finite/rational half of the remaining G1 convention dictionary.
-- The literal differentiated equation-(0.11) module already constructs the
-- centre component from the SAME J_j and T_j as
--
--        K_j = J_j T_j.
--
-- The cancellation route says that, in the source trivializations,
--
--        J_+(Y_j) Ad_{exp Y_j} = J_-(Y_j).
--
-- This module forbids a second independently chosen physical component: the
-- component consumed by the normalized 4/3 inverse is definitionally the
-- literal composeMatrix J_j T_j from the printed equation.  Once a caller
-- supplies the pointwise convention identification with the opposite inverse-
-- dexp polynomial and the source-radius coefficient data, the existing
-- source-radius theorem supplies the column bound automatically.
--
-- Thus the only G1 source leaf left after this module is the actual convention
-- identification (sign/trivialization and Bishop coefficient realization), not
-- another matrix-norm or normalization estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_; _≤_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushDifferentiatedEquation011Exact as Printed
import DASHI.Physics.YangMills.BalabanCMP109FederbushCancellationNormalizedInverseExact as Cancellation
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogSourceRadiusDefectExact as Source
import DASHI.Physics.YangMills.BalabanCMP109SU2AdCoordinateMassExact as Ad
import DASHI.Physics.YangMills.BalabanCMP109SU2AdSquareVariationMassExact as AdSq
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact as JVar
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation

record LiteralFederbushCancellationDictionary (Index : Set) : Set₁ where
  field
    differential : Printed.PhysicalFederbushEquation011Differential Index
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational
        (length (Printed.indices differential)) ≡ 1ℚ

    -- Source-radius opposite-trivialization inverse-dexp coordinates.
    c1 c2 x0 x1 x2 : Index → ℚ
    sourceRadiusData : ∀ index →
      Source.SourceRadiusPrincipalLogData
        (c1 index) (c2 index)
        (x0 index) (x1 index) (x2 index)

    oppositeInverseDexp : Index → Jacobian.Lie3Matrix
    oppositeInverseDexpIsSourcePolynomial : ∀ index row column →
      oppositeInverseDexp index row column
      ≡ JVar.principalLogAdMatrix
          (c1 index) (c2 index)
          (Ad.adMatrix (x0 index) (x1 index) (x2 index))
          (AdSq.adSquare
            (Ad.adMatrix (x0 index) (x1 index) (x2 index)))
          row column

    -- This is the one genuinely physical convention seam: identify the
    -- printed J_j T_j component with J_-(Y_j), after fixing the source sign
    -- and left/right trivializations.  No norm statement is assumed here.
    literalComponentCancellation : ∀ index row column →
      Printed.composeMatrix
        (Printed.principalLogJacobian differential index)
        (Printed.centreTransport differential index)
        row column
      ≡ oppositeInverseDexp index row column

open LiteralFederbushCancellationDictionary public

sourcePolynomial :
  ∀ {Index} → LiteralFederbushCancellationDictionary Index →
  Index → Jacobian.Lie3Matrix
sourcePolynomial dictionary index =
  JVar.principalLogAdMatrix
    (c1 dictionary index) (c2 dictionary index)
    (Ad.adMatrix
      (x0 dictionary index) (x1 dictionary index) (x2 dictionary index))
    (AdSq.adSquare
      (Ad.adMatrix
        (x0 dictionary index) (x1 dictionary index) (x2 dictionary index)))

oppositeResidualEqualsPolynomialResidual :
  ∀ {Index} (dictionary : LiteralFederbushCancellationDictionary Index)
    index row column →
  Component.logJacobianResidual
      (oppositeInverseDexp dictionary index) row column
  ≡ Component.logJacobianResidual
      (sourcePolynomial dictionary index) row column
oppositeResidualEqualsPolynomialResidual dictionary index row column =
  cong
    (λ value → value - Jacobian.identity3 row column)
    (oppositeInverseDexpIsSourcePolynomial dictionary index row column)

sourcePolynomialResidualColumnBound :
  ∀ {Index} (dictionary : LiteralFederbushCancellationDictionary Index)
    index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.logJacobianResidual (sourcePolynomial dictionary index)) column
  ≤ Source.sourcePrincipalLogColumnBound
sourcePolynomialResidualColumnBound dictionary index column =
  let
    current = sourcePolynomial dictionary index
    zero = JVar.principalLogAdMatrix
      (c1 dictionary index) Source.c2AtZero
      Source.zeroAd Source.zeroAdSquare

    raw = Source.sourcePrincipalLogVariationColumn
      (c1 dictionary index) (c2 dictionary index)
      (x0 dictionary index) (x1 dictionary index) (x2 dictionary index)
      (sourceRadiusData dictionary index) column

    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference current zero) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual current) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → cong ∣_∣
        (subst
          (λ reference →
            current row column - reference
            ≡ current row column - Jacobian.identity3 row column)
          (Source.principalLogAtZeroIsIdentity
            (c1 dictionary index) row column)
          refl))
  in
  subst
    (λ lower → lower ≤ Source.sourcePrincipalLogColumnBound)
    identify raw

oppositeInverseDexpSourceDefect :
  ∀ {Index} (dictionary : LiteralFederbushCancellationDictionary Index)
    index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.logJacobianResidual
      (oppositeInverseDexp dictionary index)) column
  ≤ Source.sourcePrincipalLogColumnBound
oppositeInverseDexpSourceDefect dictionary index column =
  let
    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual
          (oppositeInverseDexp dictionary index)) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual
          (sourcePolynomial dictionary index)) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → cong ∣_∣
        (oppositeResidualEqualsPolynomialResidual
          dictionary index row column))
  in
  subst
    (λ lower → lower ≤ Source.sourcePrincipalLogColumnBound)
    (sym identify)
    (sourcePolynomialResidualColumnBound dictionary index column)

asCancellationData :
  ∀ {Index} → LiteralFederbushCancellationDictionary Index →
  Cancellation.FederbushCancellationData Index
asCancellationData dictionary = record
  { Cancellation.FederbushCancellationData.indices =
      Printed.indices (differential dictionary)
  ; Cancellation.FederbushCancellationData.weight = weight dictionary
  ; Cancellation.FederbushCancellationData.physicalComponent = λ index →
      Printed.composeMatrix
        (Printed.principalLogJacobian (differential dictionary) index)
        (Printed.centreTransport (differential dictionary) index)
  ; Cancellation.FederbushCancellationData.oppositeInverseDexp =
      oppositeInverseDexp dictionary
  ; Cancellation.FederbushCancellationData.weightNonnegative =
      weightNonnegative dictionary
  ; Cancellation.FederbushCancellationData.normalizedWeight =
      normalizedWeight dictionary
  ; Cancellation.FederbushCancellationData.componentCancellation =
      literalComponentCancellation dictionary
  ; Cancellation.FederbushCancellationData.oppositeInverseDexpSourceDefect =
      oppositeInverseDexpSourceDefect dictionary
  }

literalFederbushCancellationInverseFourThirds :
  ∀ {Index} (dictionary : LiteralFederbushCancellationDictionary Index)
    solution source →
  Cancellation.cancellationFederbushEquation
    (asCancellationData dictionary) solution source →
  DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact.vectorL1
      Physical.lieCoordinates3 solution
  ≤ DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact.fourThirds
      * DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact.vectorL1
          Physical.lieCoordinates3 source
literalFederbushCancellationInverseFourThirds dictionary =
  Cancellation.cancellationInverseFourThirds (asCancellationData dictionary)

cmp109LiteralFederbushCancellationDictionaryLevel : ProofLevel
cmp109LiteralFederbushCancellationDictionaryLevel = machineChecked

cmp109LiteralFederbushSourceRadiusDefectTransportLevel : ProofLevel
cmp109LiteralFederbushSourceRadiusDefectTransportLevel = machineChecked

-- The sole physical G1 convention leaf remaining at this boundary is the field
-- literalComponentCancellation, i.e. the source-specific sign/trivialization
-- identification of printed J_j T_j with J_-(Y_j).  The Bishop coefficient
-- realization supplies sourceRadiusData; neither is silently promoted here.
cmp109LiteralFederbushConventionIdentificationLevel : ProofLevel
cmp109LiteralFederbushConventionIdentificationLevel = conditional
