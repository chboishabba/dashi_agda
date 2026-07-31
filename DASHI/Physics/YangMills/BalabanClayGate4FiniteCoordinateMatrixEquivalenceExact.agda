module DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact
  using (Fin; fzero; fsuc; Vec; vnil; _v∷_; lookupVec; tabulateVec;
    lookupTabulate; tabulateLookup)

------------------------------------------------------------------------
-- Concrete finite matrices on the canonical coordinate tuple.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- This closes the finite operator--matrix seam without assuming matrix-action
-- injectivity.  Matrices are literal n by n coordinate tuples, action is the
-- finite row-dot-product formula, addition acts entrywise, and equality of
-- actions is proved to imply equality of every matrix entry by testing the
-- standard coordinate vectors.
------------------------------------------------------------------------

record CommutativeSemiringLaws (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar

    addAssociative : ∀ left middle right →
      add (add left middle) right ≡ add left (add middle right)
    addCommutative : ∀ left right → add left right ≡ add right left
    addIdentityLeft : ∀ value → add zero value ≡ value
    addIdentityRight : ∀ value → add value zero ≡ value

    multiplyIdentityLeft : ∀ value → multiply one value ≡ value
    multiplyIdentityRight : ∀ value → multiply value one ≡ value
    multiplyZeroLeft : ∀ value → multiply zero value ≡ zero
    multiplyZeroRight : ∀ value → multiply value zero ≡ zero

    distributeLeft : ∀ value left right →
      multiply value (add left right)
      ≡ add (multiply value left) (multiply value right)
    distributeRight : ∀ left right value →
      multiply (add left right) value
      ≡ add (multiply left value) (multiply right value)

open CommutativeSemiringLaws public

vecExt :
  ∀ {Scalar n} {left right : Vec Scalar n} →
  (∀ index → lookupVec left index ≡ lookupVec right index) →
  left ≡ right
vecExt {n = zero} {vnil} {vnil} pointwise = refl
vecExt {n = suc n} {leftHead v∷ leftTail} {rightHead v∷ rightTail}
    pointwise with pointwise fzero
... | refl =
  cong (leftHead v∷_)
    (vecExt (λ index → pointwise (fsuc index)))

zeroVec : ∀ {Scalar} → CommutativeSemiringLaws Scalar →
  ∀ n → Vec Scalar n
zeroVec algebra zero = vnil
zeroVec algebra (suc n) = zero algebra v∷ zeroVec algebra n

addVec : ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  Vec Scalar n → Vec Scalar n → Vec Scalar n
addVec algebra vnil vnil = vnil
addVec algebra (left v∷ lefts) (right v∷ rights) =
  add algebra left right v∷ addVec algebra lefts rights

basisVector : ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  Fin n → Vec Scalar n
basisVector {n = suc n} algebra fzero =
  one algebra v∷ zeroVec algebra n
basisVector {n = suc n} algebra (fsuc index) =
  zero algebra v∷ basisVector algebra index

dot : ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  Vec Scalar n → Vec Scalar n → Scalar
dot algebra vnil vnil = zero algebra
dot algebra (left v∷ lefts) (right v∷ rights) =
  add algebra
    (multiply algebra left right)
    (dot algebra lefts rights)

dotZeroRight :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (vector : Vec Scalar n) →
  dot algebra vector (zeroVec algebra n) ≡ zero algebra
dotZeroRight algebra vnil = refl
dotZeroRight algebra (value v∷ values) =
  trans
    (cong (add algebra (multiply algebra value (zero algebra)))
      (dotZeroRight algebra values))
    (trans
      (cong (λ left → add algebra left (zero algebra))
        (multiplyZeroRight algebra value))
      (addIdentityRight algebra (zero algebra)))

dotRowBasis :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (row : Vec Scalar n) index →
  dot algebra row (basisVector algebra index)
  ≡ lookupVec row index
dotRowBasis {n = suc n} algebra (value v∷ values) fzero =
  trans
    (cong (add algebra (multiply algebra value (one algebra)))
      (dotZeroRight algebra values))
    (trans
      (cong (λ left → add algebra left (zero algebra))
        (multiplyIdentityRight algebra value))
      (addIdentityRight algebra value))
dotRowBasis {n = suc n} algebra (value v∷ values) (fsuc index) =
  trans
    (cong (add algebra (multiply algebra value (zero algebra)))
      (dotRowBasis algebra values index))
    (trans
      (cong (λ left → add algebra left (lookupVec values index))
        (multiplyZeroRight algebra value))
      (addIdentityLeft algebra (lookupVec values index)))

shuffleFour :
  ∀ {Scalar} (algebra : CommutativeSemiringLaws Scalar)
    a b c d →
  add algebra (add algebra a b) (add algebra c d)
  ≡ add algebra (add algebra a c) (add algebra b d)
shuffleFour algebra a b c d =
  trans
    (addAssociative algebra a b (add algebra c d))
    (trans
      (cong (add algebra a)
        (trans
          (sym (addAssociative algebra b c d))
          (trans
            (cong (λ value → add algebra value d)
              (addCommutative algebra b c))
            (addAssociative algebra c b d))))
      (sym (addAssociative algebra a c (add algebra b d))))

dotAddLeft :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (left right vector : Vec Scalar n) →
  dot algebra (addVec algebra left right) vector
  ≡ add algebra (dot algebra left vector) (dot algebra right vector)
dotAddLeft algebra vnil vnil vnil =
  sym (addIdentityLeft algebra (zero algebra))
dotAddLeft algebra
    (left v∷ lefts) (right v∷ rights) (value v∷ values) =
  trans
    (cong
      (add algebra
        (multiply algebra (add algebra left right) value))
      (dotAddLeft algebra lefts rights values))
    (trans
      (cong
        (λ head → add algebra head
          (add algebra
            (dot algebra lefts values)
            (dot algebra rights values)))
        (distributeRight algebra left right value))
      (shuffleFour algebra
        (multiply algebra left value)
        (multiply algebra right value)
        (dot algebra lefts values)
        (dot algebra rights values)))

FiniteMatrix : Set → Nat → Set
FiniteMatrix Scalar n = Vec (Vec Scalar n) n

addMatrix : ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  FiniteMatrix Scalar n → FiniteMatrix Scalar n → FiniteMatrix Scalar n
addMatrix algebra vnil vnil = vnil
addMatrix algebra (leftRow v∷ leftRows) (rightRow v∷ rightRows) =
  addVec algebra leftRow rightRow v∷
  addMatrix algebra leftRows rightRows

matrixAction : ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  FiniteMatrix Scalar n → Vec Scalar n → Vec Scalar n
matrixAction algebra matrix vector =
  tabulateVec (λ rowIndex →
    dot algebra (lookupVec matrix rowIndex) vector)

matrixActionEntry :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (matrix : FiniteMatrix Scalar n) vector rowIndex →
  lookupVec (matrixAction algebra matrix vector) rowIndex
  ≡ dot algebra (lookupVec matrix rowIndex) vector
matrixActionEntry algebra matrix vector rowIndex =
  lookupTabulate
    (λ index → dot algebra (lookupVec matrix index) vector)
    rowIndex

matrixActionOnBasisEntry :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (matrix : FiniteMatrix Scalar n) row column →
  lookupVec
    (matrixAction algebra matrix (basisVector algebra column)) row
  ≡ lookupVec (lookupVec matrix row) column
matrixActionOnBasisEntry algebra matrix row column =
  trans
    (matrixActionEntry algebra matrix (basisVector algebra column) row)
    (dotRowBasis algebra (lookupVec matrix row) column)

matrixActionAddPointwise :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (left right : FiniteMatrix Scalar n) vector →
  matrixAction algebra (addMatrix algebra left right) vector
  ≡ addVec algebra
      (matrixAction algebra left vector)
      (matrixAction algebra right vector)
matrixActionAddPointwise algebra left right vector =
  vecExt (λ row →
    trans
      (matrixActionEntry algebra
        (addMatrix algebra left right) vector row)
      (trans
        (dotAddLeft algebra
          (lookupVec left row) (lookupVec right row) vector)
        (sym
          (cong₂ (add algebra)
            (matrixActionEntry algebra left vector row)
            (matrixActionEntry algebra right vector row)))))

matrixActionInjective :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    {left right : FiniteMatrix Scalar n} →
  matrixAction algebra left ≡ matrixAction algebra right →
  left ≡ right
matrixActionInjective algebra {left} {right} actionEquality =
  vecExt (λ row →
    vecExt (λ column →
      trans
        (sym (matrixActionOnBasisEntry algebra left row column))
        (trans
          (cong
            (λ action →
              lookupVec (action (basisVector algebra column)) row)
            actionEquality)
          (matrixActionOnBasisEntry algebra right row column))))

record CoordinateOperator
    (Scalar : Set) (n : Nat) : Set where
  constructor coordinateOperator
  field
    operatorMatrix : FiniteMatrix Scalar n

open CoordinateOperator public

applyCoordinateOperator :
  ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  CoordinateOperator Scalar n → Vec Scalar n → Vec Scalar n
applyCoordinateOperator algebra operator =
  matrixAction algebra (operatorMatrix operator)

matrixToCoordinateOperator :
  ∀ {Scalar n} → FiniteMatrix Scalar n → CoordinateOperator Scalar n
matrixToCoordinateOperator = coordinateOperator

coordinateOperatorToMatrix :
  ∀ {Scalar n} → CoordinateOperator Scalar n → FiniteMatrix Scalar n
coordinateOperatorToMatrix = operatorMatrix

matrixOperatorRoundTrip :
  ∀ {Scalar n} (matrix : FiniteMatrix Scalar n) →
  coordinateOperatorToMatrix (matrixToCoordinateOperator matrix) ≡ matrix
matrixOperatorRoundTrip matrix = refl

operatorMatrixRoundTrip :
  ∀ {Scalar n} (operator : CoordinateOperator Scalar n) →
  matrixToCoordinateOperator (coordinateOperatorToMatrix operator) ≡ operator
operatorMatrixRoundTrip (coordinateOperator matrix) = refl

coordinateOperatorActionFaithful :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    {left right : CoordinateOperator Scalar n} →
  applyCoordinateOperator algebra left
  ≡ applyCoordinateOperator algebra right →
  left ≡ right
coordinateOperatorActionFaithful algebra
    {coordinateOperator left} {coordinateOperator right} equality =
  cong coordinateOperator (matrixActionInjective algebra equality)

addCoordinateOperator :
  ∀ {Scalar n} → CommutativeSemiringLaws Scalar →
  CoordinateOperator Scalar n → CoordinateOperator Scalar n →
  CoordinateOperator Scalar n
addCoordinateOperator algebra left right =
  coordinateOperator
    (addMatrix algebra (operatorMatrix left) (operatorMatrix right))

coordinateOperatorAddActsPointwise :
  ∀ {Scalar n} (algebra : CommutativeSemiringLaws Scalar)
    (left right : CoordinateOperator Scalar n) vector →
  applyCoordinateOperator algebra
    (addCoordinateOperator algebra left right) vector
  ≡ addVec algebra
      (applyCoordinateOperator algebra left vector)
      (applyCoordinateOperator algebra right vector)
coordinateOperatorAddActsPointwise algebra left right =
  matrixActionAddPointwise algebra
    (operatorMatrix left) (operatorMatrix right)

record ExactRestrictedCoordinateRepresentation
    (Scalar : Set) (n : Nat) : Set₁ where
  field
    scalarLaws : CommutativeSemiringLaws Scalar
    referenceMatrix remainderMatrix : FiniteMatrix Scalar n

  physicalMatrix : FiniteMatrix Scalar n
  physicalMatrix = addMatrix scalarLaws referenceMatrix remainderMatrix

  referenceOperator remainderOperator physicalOperator :
    CoordinateOperator Scalar n
  referenceOperator = coordinateOperator referenceMatrix
  remainderOperator = coordinateOperator remainderMatrix
  physicalOperator = coordinateOperator physicalMatrix

open ExactRestrictedCoordinateRepresentation public

physicalMatrixSplitsDefinitionally :
  ∀ {Scalar n}
    (representation : ExactRestrictedCoordinateRepresentation Scalar n) →
  physicalMatrix representation
  ≡ addMatrix (scalarLaws representation)
      (referenceMatrix representation)
      (remainderMatrix representation)
physicalMatrixSplitsDefinitionally representation = refl

physicalOperatorActsAsReferencePlusRemainder :
  ∀ {Scalar n}
    (representation : ExactRestrictedCoordinateRepresentation Scalar n)
    vector →
  applyCoordinateOperator (scalarLaws representation)
    (physicalOperator representation) vector
  ≡ addVec (scalarLaws representation)
      (applyCoordinateOperator (scalarLaws representation)
        (referenceOperator representation) vector)
      (applyCoordinateOperator (scalarLaws representation)
        (remainderOperator representation) vector)
physicalOperatorActsAsReferencePlusRemainder representation =
  matrixActionAddPointwise (scalarLaws representation)
    (referenceMatrix representation) (remainderMatrix representation)

finiteCoordinateMatrixActionLevel : ProofLevel
finiteCoordinateMatrixActionLevel = machineChecked

finiteMatrixActionInjectivityLevel : ProofLevel
finiteMatrixActionInjectivityLevel = machineChecked

finiteMatrixOperatorRoundTripLevel : ProofLevel
finiteMatrixOperatorRoundTripLevel = machineChecked

finiteRestrictedOperatorMatrixSplitLevel : ProofLevel
finiteRestrictedOperatorMatrixSplitLevel = machineChecked

physicalCoordinateOperatorIdentificationInputsLevel : ProofLevel
physicalCoordinateOperatorIdentificationInputsLevel = conditional
