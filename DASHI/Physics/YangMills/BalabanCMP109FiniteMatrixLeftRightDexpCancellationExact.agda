module DASHI.Physics.YangMills.BalabanCMP109FiniteMatrixLeftRightDexpCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Finite-coordinate realization of the left/right inverse-dexp identity.
-- Unlike the earlier dictionary, the desired matrix cancellation is NOT an
-- input.  It is obtained from:
--
--   dexp+ = Ad_exp o dexp-,
--   J+ dexp+ = I,
--   dexp- J- = I,
--
-- by inverse uniqueness on the literal three-coordinate action, followed by
-- evaluation on Kronecker basis vectors.  This avoids function extensionality
-- and produces the exact entrywise theorem consumed by the Federbush matrix
-- normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _+_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1

applyMatrix : Jacobian.Lie3Matrix → Jacobian.Lie3Vector → Jacobian.Lie3Vector
applyMatrix = L1.applyKernel Physical.lieCoordinates3

applyCongVector :
  ∀ matrix left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ row → applyMatrix matrix left row ≡ applyMatrix matrix right row
applyCongVector matrix left right pointwise row =
  Sums.sumRationalCong Physical.lieCoordinates3 _ _
    (λ column → cong (matrix row column *_) (pointwise column))

expandComposedColumn :
  ∀ outer inner vector row column →
  Component.matrixCompose outer inner row column * vector column
  ≡ Sums.sumRational Physical.lieCoordinates3
      (λ middle → outer row middle * inner middle column * vector column)
expandComposedColumn outer inner vector row column =
  let
    term = λ middle → outer row middle * inner middle column
    commuteOuter :
      Component.matrixCompose outer inner row column * vector column
      ≡ vector column * Component.matrixCompose outer inner row column
    commuteOuter = ℚP.*-comm
      (Component.matrixCompose outer inner row column) (vector column)
    distribute :
      vector column * Component.matrixCompose outer inner row column
      ≡ Sums.sumRational Physical.lieCoordinates3
          (λ middle → vector column * term middle)
    distribute = sym
      (Sums.sumRationalScale
        (vector column) Physical.lieCoordinates3 term)
    commuteInside :
      Sums.sumRational Physical.lieCoordinates3
          (λ middle → vector column * term middle)
      ≡ Sums.sumRational Physical.lieCoordinates3
          (λ middle → outer row middle * inner middle column * vector column)
    commuteInside =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (λ middle → ℚRing.solve-∀
          (outer row middle) (inner middle column) (vector column))
  in trans commuteOuter (trans distribute commuteInside)

factorOuterAtMiddle :
  ∀ outer inner vector row middle →
  Sums.sumRational Physical.lieCoordinates3
    (λ column → outer row middle * inner middle column * vector column)
  ≡ outer row middle * applyMatrix inner vector middle
factorOuterAtMiddle outer inner vector row middle =
  trans
    (Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ column → ℚRing.solve-∀
        (outer row middle) (inner middle column) (vector column)))
    (Sums.sumRationalScale
      (outer row middle) Physical.lieCoordinates3
      (λ column → inner middle column * vector column))

applyMatrixComposeExact :
  ∀ outer inner vector row →
  applyMatrix (Component.matrixCompose outer inner) vector row
  ≡ applyMatrix outer (applyMatrix inner vector) row
applyMatrixComposeExact outer inner vector row =
  let
    expandColumns =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (expandComposedColumn outer inner vector row)
    swap = Fubini.sumSwap
      Physical.lieCoordinates3 Physical.lieCoordinates3
      (λ column middle →
        outer row middle * inner middle column * vector column)
    factor = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (factorOuterAtMiddle outer inner vector row)
  in trans expandColumns (trans swap factor)

basisVector : Physical.LieCoordinate3 → Jacobian.Lie3Vector
basisVector column middle =
  Coordinates.kroneckerDelta
    Coordinates.lieCoordinateDecidableEquality column middle

applyMatrixBasisExact : ∀ matrix row column →
  applyMatrix matrix (basisVector column) row ≡ matrix row column
applyMatrixBasisExact matrix row column =
  trans
    (Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ middle → ℚP.*-comm
        (matrix row middle)
        (Coordinates.kroneckerDelta
          Coordinates.lieCoordinateDecidableEquality column middle)))
    (Coordinates.deltaSumIdentity
      Coordinates.lieCoordinateDecidableEquality
      Coordinates.lieCoordinatesDuplicateFree
      column
      (Jacobian.lieCoordinateComplete column)
      (matrix row))

record MatrixLeftRightDexpCancellationData
    (Jplus adjointExp Jminus : Jacobian.Lie3Matrix) : Set₁ where
  field
    dexpPlus dexpMinus : Jacobian.Lie3Matrix

    plusIsAdjointOfMinus : ∀ vector row →
      applyMatrix dexpPlus vector row
      ≡ applyMatrix adjointExp (applyMatrix dexpMinus vector) row

    JplusAfterDexpPlus : ∀ vector row →
      applyMatrix Jplus (applyMatrix dexpPlus vector) row ≡ vector row

    dexpMinusAfterJminus : ∀ vector row →
      applyMatrix dexpMinus (applyMatrix Jminus vector) row ≡ vector row

open MatrixLeftRightDexpCancellationData public

candidateAfterDexpMinus :
  ∀ {Jplus adjointExp Jminus}
    (dataSet : MatrixLeftRightDexpCancellationData Jplus adjointExp Jminus)
    vector row →
  applyMatrix Jplus
    (applyMatrix adjointExp (applyMatrix (dexpMinus dataSet) vector)) row
  ≡ vector row
candidateAfterDexpMinus {Jplus} dataSet vector row =
  trans
    (applyCongVector Jplus _ _
      (λ coordinate → sym
        (plusIsAdjointOfMinus dataSet vector coordinate)) row)
    (JplusAfterDexpPlus dataSet vector row)

matrixInverseUniqueAction :
  ∀ forward leftInverse rightInverse →
  (∀ vector row →
    applyMatrix forward (applyMatrix rightInverse vector) row ≡ vector row) →
  (∀ vector row →
    applyMatrix leftInverse (applyMatrix forward vector) row ≡ vector row) →
  ∀ vector row →
  applyMatrix leftInverse vector row ≡ applyMatrix rightInverse vector row
matrixInverseUniqueAction forward leftInverse rightInverse
    forwardAfterRight leftAfterForward vector row =
  trans
    (applyCongVector leftInverse _ _
      (λ coordinate → sym (forwardAfterRight vector coordinate)) row)
    (leftAfterForward (applyMatrix rightInverse vector) row)

leftRightDexpActionCancellation :
  ∀ {Jplus adjointExp Jminus}
    (dataSet : MatrixLeftRightDexpCancellationData Jplus adjointExp Jminus)
    vector row →
  applyMatrix (Component.matrixCompose Jplus adjointExp) vector row
  ≡ applyMatrix Jminus vector row
leftRightDexpActionCancellation {Jplus} {adjointExp} {Jminus} dataSet vector row =
  trans
    (applyMatrixComposeExact Jplus adjointExp vector row)
    (matrixInverseUniqueAction
      (dexpMinus dataSet)
      (Component.matrixCompose Jplus adjointExp)
      Jminus
      (dexpMinusAfterJminus dataSet)
      (λ selected selectedRow →
        trans
          (applyMatrixComposeExact Jplus adjointExp
            (applyMatrix (dexpMinus dataSet) selected) selectedRow)
          (candidateAfterDexpMinus dataSet selected selectedRow))
      vector row)

leftRightDexpMatrixCancellation :
  ∀ {Jplus adjointExp Jminus}
    (dataSet : MatrixLeftRightDexpCancellationData Jplus adjointExp Jminus)
    row column →
  Component.matrixCompose Jplus adjointExp row column ≡ Jminus row column
leftRightDexpMatrixCancellation {Jplus} {adjointExp} {Jminus} dataSet row column =
  trans
    (sym (applyMatrixBasisExact
      (Component.matrixCompose Jplus adjointExp) row column))
    (trans
      (leftRightDexpActionCancellation dataSet (basisVector column) row)
      (applyMatrixBasisExact Jminus row column))

cmp109FiniteMatrixCompositionActionLevel : ProofLevel
cmp109FiniteMatrixCompositionActionLevel = machineChecked

cmp109FiniteMatrixInverseUniquenessLevel : ProofLevel
cmp109FiniteMatrixInverseUniquenessLevel = machineChecked

cmp109FiniteMatrixLeftRightDexpCancellationLevel : ProofLevel
cmp109FiniteMatrixLeftRightDexpCancellationLevel = machineChecked
