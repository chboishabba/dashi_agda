module DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedAdjointFubiniExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite weighted-adjoint derivation by an explicit Fubini interchange.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik 140
-- (1911), 1--28. No DOI recorded.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- A local weighted transpose identity is not yet the global adjoint theorem:
-- one must interchange the complete finite input and output sums.  The module
-- proves that interchange from commutative-monoid laws and then derives the
-- global weighted pairing identity.  Thus the weighted adjoint formula needs
-- only an entrywise proof; no second global-adjoint assumption remains.
------------------------------------------------------------------------

record AdditiveCommutativeMonoid (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar

    addAssociative : ∀ left middle right →
      add (add left middle) right ≡ add left (add middle right)
    addCommutative : ∀ left right → add left right ≡ add right left
    addIdentityLeft : ∀ value → add zero value ≡ value
    addIdentityRight : ∀ value → add value zero ≡ value

open AdditiveCommutativeMonoid public

sumList :
  ∀ {A Scalar} →
  AdditiveCommutativeMonoid Scalar →
  List A → (A → Scalar) → Scalar
sumList algebra [] term = zero algebra
sumList algebra (value ∷ values) term =
  add algebra (term value) (sumList algebra values term)

sumCong :
  ∀ {A Scalar}
    (algebra : AdditiveCommutativeMonoid Scalar)
    (values : List A) (left right : A → Scalar) →
  (∀ value → left value ≡ right value) →
  sumList algebra values left ≡ sumList algebra values right
sumCong algebra [] left right pointwise = refl
sumCong algebra (value ∷ values) left right pointwise =
  cong₂ (add algebra)
    (pointwise value)
    (sumCong algebra values left right pointwise)

shuffleFour :
  ∀ {Scalar}
    (algebra : AdditiveCommutativeMonoid Scalar)
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

sumPointwiseAdd :
  ∀ {A Scalar}
    (algebra : AdditiveCommutativeMonoid Scalar)
    (values : List A) (left right : A → Scalar) →
  sumList algebra values
    (λ value → add algebra (left value) (right value))
  ≡ add algebra
      (sumList algebra values left)
      (sumList algebra values right)
sumPointwiseAdd algebra [] left right =
  sym (addIdentityLeft algebra (zero algebra))
sumPointwiseAdd algebra (value ∷ values) left right =
  trans
    (cong
      (add algebra (add algebra (left value) (right value)))
      (sumPointwiseAdd algebra values left right))
    (shuffleFour algebra
      (left value) (right value)
      (sumList algebra values left)
      (sumList algebra values right))

sumZero :
  ∀ {A Scalar}
    (algebra : AdditiveCommutativeMonoid Scalar)
    (values : List A) →
  sumList algebra values (λ value → zero algebra) ≡ zero algebra
sumZero algebra [] = refl
sumZero algebra (value ∷ values) =
  trans
    (cong (add algebra (zero algebra)) (sumZero algebra values))
    (addIdentityLeft algebra (zero algebra))

finiteFubini :
  ∀ {A B Scalar}
    (algebra : AdditiveCommutativeMonoid Scalar)
    (leftValues : List A) (rightValues : List B)
    (term : A → B → Scalar) →
  sumList algebra leftValues
    (λ left → sumList algebra rightValues (term left))
  ≡ sumList algebra rightValues
      (λ right → sumList algebra leftValues
        (λ left → term left right))
finiteFubini algebra [] rightValues term =
  sym (sumZero algebra rightValues)
finiteFubini algebra (left ∷ leftValues) rightValues term =
  trans
    (cong
      (add algebra (sumList algebra rightValues (term left)))
      (finiteFubini algebra leftValues rightValues term))
    (sym
      (sumPointwiseAdd algebra rightValues
        (term left)
        (λ right → sumList algebra leftValues
          (λ remaining → term remaining right))))

record FiniteWeightedAdjointContributionData
    (Input Output FineValue CoarseValue Scalar : Set) : Set₁ where
  field
    scalarAdditive : AdditiveCommutativeMonoid Scalar

    inputs : List Input
    outputs : List Output

    primalWeightedContribution :
      Output → Input → FineValue → CoarseValue → Scalar

    adjointWeightedContribution :
      Input → Output → FineValue → CoarseValue → Scalar

    localWeightedAdjointIdentity :
      ∀ output input fineValue coarseValue →
      primalWeightedContribution output input fineValue coarseValue
      ≡ adjointWeightedContribution input output fineValue coarseValue

open FiniteWeightedAdjointContributionData public

primalWeightedPairing :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  FiniteWeightedAdjointContributionData
    Input Output FineValue CoarseValue Scalar →
  (Input → FineValue) → (Output → CoarseValue) → Scalar
primalWeightedPairing dataSet fineField coarseField =
  sumList (scalarAdditive dataSet) (outputs dataSet)
    (λ output →
      sumList (scalarAdditive dataSet) (inputs dataSet)
        (λ input →
          primalWeightedContribution dataSet output input
            (fineField input) (coarseField output)))

adjointWeightedPairing :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  FiniteWeightedAdjointContributionData
    Input Output FineValue CoarseValue Scalar →
  (Input → FineValue) → (Output → CoarseValue) → Scalar
adjointWeightedPairing dataSet fineField coarseField =
  sumList (scalarAdditive dataSet) (inputs dataSet)
    (λ input →
      sumList (scalarAdditive dataSet) (outputs dataSet)
        (λ output →
          adjointWeightedContribution dataSet input output
            (fineField input) (coarseField output)))

globalWeightedAdjointIdentity :
  ∀ {Input Output FineValue CoarseValue Scalar}
    (dataSet : FiniteWeightedAdjointContributionData
      Input Output FineValue CoarseValue Scalar)
    fineField coarseField →
  primalWeightedPairing dataSet fineField coarseField
  ≡ adjointWeightedPairing dataSet fineField coarseField
globalWeightedAdjointIdentity dataSet fineField coarseField =
  trans
    (sumCong (scalarAdditive dataSet) (outputs dataSet)
      (λ output →
        sumList (scalarAdditive dataSet) (inputs dataSet)
          (λ input →
            primalWeightedContribution dataSet output input
              (fineField input) (coarseField output)))
      (λ output →
        sumList (scalarAdditive dataSet) (inputs dataSet)
          (λ input →
            adjointWeightedContribution dataSet input output
              (fineField input) (coarseField output)))
      (λ output →
        sumCong (scalarAdditive dataSet) (inputs dataSet)
          (λ input →
            primalWeightedContribution dataSet output input
              (fineField input) (coarseField output))
          (λ input →
            adjointWeightedContribution dataSet input output
              (fineField input) (coarseField output))
          (λ input →
            localWeightedAdjointIdentity dataSet output input
              (fineField input) (coarseField output))))
    (finiteFubini (scalarAdditive dataSet)
      (outputs dataSet) (inputs dataSet)
      (λ output input →
        adjointWeightedContribution dataSet input output
          (fineField input) (coarseField output)))

finiteAdditiveFubiniLevel : ProofLevel
finiteAdditiveFubiniLevel = machineChecked

weightedAdjointLocalToGlobalLevel : ProofLevel
weightedAdjointLocalToGlobalLevel = machineChecked

weightedAdjointFiniteSumOrderLevel : ProofLevel
weightedAdjointFiniteSumOrderLevel = machineChecked

physicalWeightedAdjointEntryFormulaInputsLevel : ProofLevel
physicalWeightedAdjointEntryFormulaInputsLevel = conditional

physicalFineCoarsePairingIdentificationInputsLevel : ProofLevel
physicalFineCoarsePairingIdentificationInputsLevel = conditional
