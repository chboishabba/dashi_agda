module DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixCompositionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact as Free
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact as Coordinate

------------------------------------------------------------------------
-- Exact matrix composition and identity on the canonical coordinate carrier.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The preceding coordinate module proves faithfulness and matrix/operator
-- round trips.  This module closes the remaining elementary laws: literal
-- finite matrix multiplication acts as operator composition, and the literal
-- standard-basis matrix acts as the identity operator.  All sums are structural
-- recursions over the finite `Vec` carrier; no matrix-action or Fubini theorem is
-- assumed.
------------------------------------------------------------------------

record MatrixMultiplicationLaws (Scalar : Set) : Set₁ where
  field
    semiring : Coordinate.CommutativeSemiringLaws Scalar
    multiplyAssociative : ∀ left middle right →
      Coordinate.multiply semiring
        (Coordinate.multiply semiring left middle) right
      ≡ Coordinate.multiply semiring left
          (Coordinate.multiply semiring middle right)

open MatrixMultiplicationLaws public

scaleVec :
  ∀ {Scalar n} → MatrixMultiplicationLaws Scalar →
  Scalar → Free.Vec Scalar n → Free.Vec Scalar n
scaleVec laws scalar Free.vnil = Free.vnil
scaleVec laws scalar (value Free.v∷ values) =
  Coordinate.multiply (semiring laws) scalar value Free.v∷
  scaleVec laws scalar values

dotZeroLeft :
  ∀ {Scalar n} (laws : MatrixMultiplicationLaws Scalar)
    (vector : Free.Vec Scalar n) →
  Coordinate.dot (semiring laws)
    (Coordinate.zeroVec (semiring laws) n) vector
  ≡ Coordinate.zero (semiring laws)
dotZeroLeft laws Free.vnil = refl
dotZeroLeft laws (value Free.v∷ values) =
  trans
    (cong
      (Coordinate.add (semiring laws)
        (Coordinate.multiply (semiring laws)
          (Coordinate.zero (semiring laws)) value))
      (dotZeroLeft laws values))
    (trans
      (cong
        (λ head → Coordinate.add (semiring laws) head
          (Coordinate.zero (semiring laws)))
        (Coordinate.multiplyZeroLeft (semiring laws) value))
      (Coordinate.addIdentityRight (semiring laws)
        (Coordinate.zero (semiring laws))))

dotScaleLeft :
  ∀ {Scalar n} (laws : MatrixMultiplicationLaws Scalar)
    scalar (left right : Free.Vec Scalar n) →
  Coordinate.dot (semiring laws) (scaleVec laws scalar left) right
  ≡ Coordinate.multiply (semiring laws) scalar
      (Coordinate.dot (semiring laws) left right)
dotScaleLeft laws scalar Free.vnil Free.vnil =
  sym (Coordinate.multiplyZeroRight (semiring laws) scalar)
dotScaleLeft laws scalar
    (left Free.v∷ lefts) (right Free.v∷ rights) =
  trans
    (cong
      (Coordinate.add (semiring laws)
        (Coordinate.multiply (semiring laws)
          (Coordinate.multiply (semiring laws) scalar left) right))
      (dotScaleLeft laws scalar lefts rights))
    (trans
      (cong
        (λ head → Coordinate.add (semiring laws) head
          (Coordinate.multiply (semiring laws) scalar
            (Coordinate.dot (semiring laws) lefts rights)))
        (multiplyAssociative laws scalar left right))
      (sym
        (Coordinate.distributeLeft (semiring laws) scalar
          (Coordinate.multiply (semiring laws) left right)
          (Coordinate.dot (semiring laws) lefts rights))))

rectangularAction :
  ∀ {Scalar rows columns} →
  Coordinate.CommutativeSemiringLaws Scalar →
  Free.Vec (Free.Vec Scalar columns) rows →
  Free.Vec Scalar columns → Free.Vec Scalar rows
rectangularAction algebra Free.vnil vector = Free.vnil
rectangularAction algebra (row Free.v∷ rows) vector =
  Coordinate.dot algebra row vector Free.v∷
  rectangularAction algebra rows vector

lookupRectangularAction :
  ∀ {Scalar rows columns}
    (algebra : Coordinate.CommutativeSemiringLaws Scalar)
    (matrix : Free.Vec (Free.Vec Scalar columns) rows)
    vector row →
  Free.lookupVec (rectangularAction algebra matrix vector) row
  ≡ Coordinate.dot algebra (Free.lookupVec matrix row) vector
lookupRectangularAction {rows = suc rows} algebra
    (matrixRow Free.v∷ matrixRows) vector Free.fzero = refl
lookupRectangularAction {rows = suc rows} algebra
    (matrixRow Free.v∷ matrixRows) vector (Free.fsuc row) =
  lookupRectangularAction algebra matrixRows vector row

rowTimesMatrix :
  ∀ {Scalar rows columns} →
  MatrixMultiplicationLaws Scalar →
  Free.Vec Scalar rows →
  Free.Vec (Free.Vec Scalar columns) rows →
  Free.Vec Scalar columns
rowTimesMatrix {columns = columns} laws Free.vnil Free.vnil =
  Coordinate.zeroVec (semiring laws) columns
rowTimesMatrix laws
    (coefficient Free.v∷ coefficients)
    (row Free.v∷ rows) =
  Coordinate.addVec (semiring laws)
    (scaleVec laws coefficient row)
    (rowTimesMatrix laws coefficients rows)

dotRowTimesMatrix :
  ∀ {Scalar rows columns}
    (laws : MatrixMultiplicationLaws Scalar)
    (coefficients : Free.Vec Scalar rows)
    (matrix : Free.Vec (Free.Vec Scalar columns) rows)
    (vector : Free.Vec Scalar columns) →
  Coordinate.dot (semiring laws)
    (rowTimesMatrix laws coefficients matrix) vector
  ≡ Coordinate.dot (semiring laws) coefficients
      (rectangularAction (semiring laws) matrix vector)
dotRowTimesMatrix {columns = columns} laws Free.vnil Free.vnil vector =
  dotZeroLeft laws vector
dotRowTimesMatrix laws
    (coefficient Free.v∷ coefficients)
    (row Free.v∷ rows) vector =
  trans
    (Coordinate.dotAddLeft (semiring laws)
      (scaleVec laws coefficient row)
      (rowTimesMatrix laws coefficients rows)
      vector)
    (trans
      (cong₂ (Coordinate.add (semiring laws))
        (dotScaleLeft laws coefficient row vector)
        (dotRowTimesMatrix laws coefficients rows vector))
      refl)

multiplyRows :
  ∀ {Scalar outputRows dimension} →
  MatrixMultiplicationLaws Scalar →
  Free.Vec (Free.Vec Scalar dimension) outputRows →
  Coordinate.FiniteMatrix Scalar dimension →
  Free.Vec (Free.Vec Scalar dimension) outputRows
multiplyRows laws Free.vnil right = Free.vnil
multiplyRows laws (row Free.v∷ rows) right =
  rowTimesMatrix laws row right Free.v∷
  multiplyRows laws rows right

lookupMultiplyRows :
  ∀ {Scalar outputRows dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (left : Free.Vec (Free.Vec Scalar dimension) outputRows)
    right row →
  Free.lookupVec (multiplyRows laws left right) row
  ≡ rowTimesMatrix laws (Free.lookupVec left row) right
lookupMultiplyRows {outputRows = suc rows} laws
    (leftRow Free.v∷ leftRows) right Free.fzero = refl
lookupMultiplyRows {outputRows = suc rows} laws
    (leftRow Free.v∷ leftRows) right (Free.fsuc row) =
  lookupMultiplyRows laws leftRows right row

multiplyMatrix :
  ∀ {Scalar dimension} →
  MatrixMultiplicationLaws Scalar →
  Coordinate.FiniteMatrix Scalar dimension →
  Coordinate.FiniteMatrix Scalar dimension →
  Coordinate.FiniteMatrix Scalar dimension
multiplyMatrix = multiplyRows

rectangularProductAction :
  ∀ {Scalar outputRows dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (left : Free.Vec (Free.Vec Scalar dimension) outputRows)
    (right : Coordinate.FiniteMatrix Scalar dimension)
    vector →
  rectangularAction (semiring laws)
    (multiplyRows laws left right) vector
  ≡ rectangularAction (semiring laws) left
      (rectangularAction (semiring laws) right vector)
rectangularProductAction laws Free.vnil right vector = refl
rectangularProductAction laws
    (leftRow Free.v∷ leftRows) right vector =
  cong₂ Free._v∷_
    (dotRowTimesMatrix laws leftRow right vector)
    (rectangularProductAction laws leftRows right vector)

rectangularActionEqualsMatrixAction :
  ∀ {Scalar dimension}
    (algebra : Coordinate.CommutativeSemiringLaws Scalar)
    (matrix : Coordinate.FiniteMatrix Scalar dimension)
    vector →
  rectangularAction algebra matrix vector
  ≡ Coordinate.matrixAction algebra matrix vector
rectangularActionEqualsMatrixAction algebra matrix vector =
  Coordinate.vecExt (λ row →
    trans
      (lookupRectangularAction algebra matrix vector row)
      (sym (Coordinate.matrixActionEntry algebra matrix vector row)))

matrixProductActsAsComposition :
  ∀ {Scalar dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (left right : Coordinate.FiniteMatrix Scalar dimension)
    vector →
  Coordinate.matrixAction (semiring laws)
    (multiplyMatrix laws left right) vector
  ≡ Coordinate.matrixAction (semiring laws) left
      (Coordinate.matrixAction (semiring laws) right vector)
matrixProductActsAsComposition laws left right vector =
  trans
    (sym
      (rectangularActionEqualsMatrixAction (semiring laws)
        (multiplyMatrix laws left right) vector))
    (trans
      (rectangularProductAction laws left right vector)
      (trans
        (cong
          (rectangularAction (semiring laws) left)
          (rectangularActionEqualsMatrixAction
            (semiring laws) right vector))
        (rectangularActionEqualsMatrixAction (semiring laws) left
          (Coordinate.matrixAction (semiring laws) right vector))))

dotBasisVector :
  ∀ {Scalar dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (index : Free.Fin dimension)
    (vector : Free.Vec Scalar dimension) →
  Coordinate.dot (semiring laws)
    (Coordinate.basisVector (semiring laws) index) vector
  ≡ Free.lookupVec vector index
dotBasisVector {dimension = suc dimension} laws Free.fzero
    (value Free.v∷ values) =
  trans
    (cong
      (Coordinate.add (semiring laws)
        (Coordinate.multiply (semiring laws)
          (Coordinate.one (semiring laws)) value))
      (dotZeroLeft laws values))
    (trans
      (cong
        (λ head → Coordinate.add (semiring laws) head
          (Coordinate.zero (semiring laws)))
        (Coordinate.multiplyIdentityLeft (semiring laws) value))
      (Coordinate.addIdentityRight (semiring laws) value))
dotBasisVector {dimension = suc dimension} laws (Free.fsuc index)
    (value Free.v∷ values) =
  trans
    (cong
      (Coordinate.add (semiring laws)
        (Coordinate.multiply (semiring laws)
          (Coordinate.zero (semiring laws)) value))
      (dotBasisVector laws index values))
    (trans
      (cong
        (λ head → Coordinate.add (semiring laws) head
          (Free.lookupVec values index))
        (Coordinate.multiplyZeroLeft (semiring laws) value))
      (Coordinate.addIdentityLeft (semiring laws)
        (Free.lookupVec values index)))

identityMatrix :
  ∀ {Scalar dimension} →
  MatrixMultiplicationLaws Scalar →
  Coordinate.FiniteMatrix Scalar dimension
identityMatrix laws =
  Free.tabulateVec (Coordinate.basisVector (semiring laws))

identityMatrixActsIdentically :
  ∀ {Scalar dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (vector : Free.Vec Scalar dimension) →
  Coordinate.matrixAction (semiring laws) (identityMatrix laws) vector
  ≡ vector
identityMatrixActsIdentically laws vector =
  Coordinate.vecExt (λ row →
    trans
      (Coordinate.matrixActionEntry (semiring laws)
        (identityMatrix laws) vector row)
      (trans
        (cong
          (λ selectedRow → Coordinate.dot (semiring laws) selectedRow vector)
          (Free.lookupTabulate
            (Coordinate.basisVector (semiring laws)) row))
        (dotBasisVector laws row vector)))

composeCoordinateOperator :
  ∀ {Scalar dimension} →
  MatrixMultiplicationLaws Scalar →
  Coordinate.CoordinateOperator Scalar dimension →
  Coordinate.CoordinateOperator Scalar dimension →
  Coordinate.CoordinateOperator Scalar dimension
composeCoordinateOperator laws left right =
  Coordinate.coordinateOperator
    (multiplyMatrix laws
      (Coordinate.operatorMatrix left)
      (Coordinate.operatorMatrix right))

coordinateOperatorCompositionExact :
  ∀ {Scalar dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    (left right : Coordinate.CoordinateOperator Scalar dimension)
    vector →
  Coordinate.applyCoordinateOperator (semiring laws)
    (composeCoordinateOperator laws left right) vector
  ≡ Coordinate.applyCoordinateOperator (semiring laws) left
      (Coordinate.applyCoordinateOperator (semiring laws) right vector)
coordinateOperatorCompositionExact laws left right =
  matrixProductActsAsComposition laws
    (Coordinate.operatorMatrix left)
    (Coordinate.operatorMatrix right)

identityCoordinateOperator :
  ∀ {Scalar dimension} →
  MatrixMultiplicationLaws Scalar →
  Coordinate.CoordinateOperator Scalar dimension
identityCoordinateOperator laws =
  Coordinate.coordinateOperator (identityMatrix laws)

identityCoordinateOperatorExact :
  ∀ {Scalar dimension}
    (laws : MatrixMultiplicationLaws Scalar)
    vector →
  Coordinate.applyCoordinateOperator (semiring laws)
    (identityCoordinateOperator laws) vector
  ≡ vector
identityCoordinateOperatorExact = identityMatrixActsIdentically

finiteMatrixProductActionLevel : ProofLevel
finiteMatrixProductActionLevel = machineChecked

finiteMatrixIdentityActionLevel : ProofLevel
finiteMatrixIdentityActionLevel = machineChecked

finiteOperatorCompositionMatrixLevel : ProofLevel
finiteOperatorCompositionMatrixLevel = machineChecked

finiteOperatorIdentityMatrixLevel : ProofLevel
finiteOperatorIdentityMatrixLevel = machineChecked
