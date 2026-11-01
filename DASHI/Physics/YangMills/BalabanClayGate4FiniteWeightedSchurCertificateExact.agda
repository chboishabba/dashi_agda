module DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedSchurCertificateExact where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; _∈_; here; there; FiniteEnumeration; elements; complete)

------------------------------------------------------------------------
-- Executable finite certification of weighted row and column inequalities.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik 140
-- (1911), 1--28. No DOI recorded.
--
-- For a finite periodic carrier, every weighted row and column comparison can
-- be decided.  A successful `All` certificate is lifted through completeness of
-- the enumeration to a theorem for every input/output index.  This module does
-- not approximate a scalar or invent an interval method; it supplies the exact
-- consumer for a future rational or outward-rounded implementation.
------------------------------------------------------------------------

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

allFromMembership :
  ∀ {A : Set} {Predicate : A → Set} {value values} →
  value ∈ values → All Predicate values → Predicate value
allFromMembership here (allCons proof rest) = proof
allFromMembership (there member) (allCons proof rest) =
  allFromMembership member rest

decideAll :
  ∀ {A : Set} {Predicate : A → Set} →
  ((value : A) → Dec (Predicate value)) →
  (values : List A) → Dec (All Predicate values)
decideAll decide [] = yes allNil
decideAll decide (value ∷ values) with decide value | decideAll decide values
... | yes proof | yes rest = yes (allCons proof rest)
... | no refute | restDecision = no λ where
      (allCons proof rest) → refute proof
... | yes proof | no refuteRest = no λ where
      (allCons head rest) → refuteRest rest

record FiniteWeightedComparisonData
    (Input Output Scalar : Set) : Set₁ where
  field
    inputFinite : FiniteEnumeration Input
    outputFinite : FiniteEnumeration Output

    weightedRowSum : Output → Scalar
    weightedColumnSum : Input → Scalar
    rowUpper : Output → Scalar
    columnUpper : Input → Scalar

    LessEqual : Scalar → Scalar → Set
    lessEqualDecidable : ∀ left right → Dec (LessEqual left right)

open FiniteWeightedComparisonData public

RowBound :
  ∀ {Input Output Scalar} →
  FiniteWeightedComparisonData Input Output Scalar →
  Output → Set
RowBound dataSet output =
  LessEqual dataSet
    (weightedRowSum dataSet output)
    (rowUpper dataSet output)

ColumnBound :
  ∀ {Input Output Scalar} →
  FiniteWeightedComparisonData Input Output Scalar →
  Input → Set
ColumnBound dataSet input =
  LessEqual dataSet
    (weightedColumnSum dataSet input)
    (columnUpper dataSet input)

checkAllWeightedRows :
  ∀ {Input Output Scalar}
    (dataSet : FiniteWeightedComparisonData Input Output Scalar) →
  Dec (All (RowBound dataSet) (elements (outputFinite dataSet)))
checkAllWeightedRows dataSet =
  decideAll
    (λ output → lessEqualDecidable dataSet
      (weightedRowSum dataSet output)
      (rowUpper dataSet output))
    (elements (outputFinite dataSet))

checkAllWeightedColumns :
  ∀ {Input Output Scalar}
    (dataSet : FiniteWeightedComparisonData Input Output Scalar) →
  Dec (All (ColumnBound dataSet) (elements (inputFinite dataSet)))
checkAllWeightedColumns dataSet =
  decideAll
    (λ input → lessEqualDecidable dataSet
      (weightedColumnSum dataSet input)
      (columnUpper dataSet input))
    (elements (inputFinite dataSet))

record AcceptedFiniteWeightedCertificate
    {Input Output Scalar : Set}
    (dataSet : FiniteWeightedComparisonData Input Output Scalar) : Set₁ where
  field
    allRowsAccepted :
      All (RowBound dataSet) (elements (outputFinite dataSet))
    allColumnsAccepted :
      All (ColumnBound dataSet) (elements (inputFinite dataSet))

open AcceptedFiniteWeightedCertificate public

acceptedRowBoundEverywhere :
  ∀ {Input Output Scalar}
    {dataSet : FiniteWeightedComparisonData Input Output Scalar} →
  AcceptedFiniteWeightedCertificate dataSet →
  ∀ output → RowBound dataSet output
acceptedRowBoundEverywhere {dataSet = dataSet} certificate output =
  allFromMembership
    (complete (outputFinite dataSet) output)
    (allRowsAccepted certificate)

acceptedColumnBoundEverywhere :
  ∀ {Input Output Scalar}
    {dataSet : FiniteWeightedComparisonData Input Output Scalar} →
  AcceptedFiniteWeightedCertificate dataSet →
  ∀ input → ColumnBound dataSet input
acceptedColumnBoundEverywhere {dataSet = dataSet} certificate input =
  allFromMembership
    (complete (inputFinite dataSet) input)
    (allColumnsAccepted certificate)

record WeightedCertificateReceipt
    {Input Output Scalar : Set}
    (dataSet : FiniteWeightedComparisonData Input Output Scalar) : Set₁ where
  field
    certificate : AcceptedFiniteWeightedCertificate dataSet

    KernelAndWeightsMatchPhysicalMeaning : Set
    kernelAndWeightsMatchPhysicalMeaning :
      KernelAndWeightsMatchPhysicalMeaning

    ArithmeticWasExactOrOutwardRounded : Set
    arithmeticWasExactOrOutwardRounded :
      ArithmeticWasExactOrOutwardRounded

open WeightedCertificateReceipt public

finiteWeightedRowCertificateLevel : ProofLevel
finiteWeightedRowCertificateLevel = machineChecked

finiteWeightedColumnCertificateLevel : ProofLevel
finiteWeightedColumnCertificateLevel = machineChecked

finiteCertificateUniversalLiftLevel : ProofLevel
finiteCertificateUniversalLiftLevel = machineChecked

physicalWeightedCertificateArithmeticInputsLevel : ProofLevel
physicalWeightedCertificateArithmeticInputsLevel = conditional

physicalWeightedCertificateMeaningInputsLevel : ProofLevel
physicalWeightedCertificateMeaningInputsLevel = conditional
