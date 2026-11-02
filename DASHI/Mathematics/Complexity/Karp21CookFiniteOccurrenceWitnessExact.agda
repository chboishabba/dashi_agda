module DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact where

------------------------------------------------------------------------
-- K00: FINITE SAT WITNESS WITHOUT ENUMERATING ALL NAT VARIABLE IDS.
--
-- Reuse Cook.BooleanFormula / Cook.evaluate / Cook.Satisfiable.
-- A Cook variable has an arbitrary Nat index. Allocating a full
-- vector of length (maxIndex + 1) could be exponentially larger than
-- the size of the binary formula. Instead store exactly ONE bit for
-- each syntactic variable OCCURRENCE, in preorder.
--
-- Repeated occurrences of the same index are read via the FIRST
-- occurrence. This induces one genuine total Cook.Assignment.
-- A satisfying assignment projects to finite bits, and that finite
-- sequence reconstructs an assignment with the SAME formula verdict.
-- Conversely any finite bit sequence with an accepted reconstructed
-- evaluation is a genuine Cook.Satisfiable witness.
--
-- This is a SAME-FORMULA mathematical equivalence, not yet a verifier
-- machine-cost proof or a polynomial bound in strict SAT Word length.
-- The certificate's exact count is the number of variable occurrences.
--
-- Mathematical source: Cook 1971; Leonid Levin 1973 search framework.
-- Prior in-repo source owner: CookLevinCircuitGCTBoundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
import Data.Nat.Properties as NatP
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse

formulaVariables : Cook.BooleanFormula → List Nat
formulaVariables (Cook.variable i) = i ∷ []
formulaVariables (Cook.constant value) = []
formulaVariables (Cook.negate formula) = formulaVariables formula
formulaVariables (Cook.conjunction left right) =
  formulaVariables left ++ formulaVariables right
formulaVariables (Cook.disjunction left right) =
  formulaVariables left ++ formulaVariables right

projectBits : List Nat → Cook.Assignment → List Bool
projectBits [] assignment = []
projectBits (i ∷ rest) assignment =
  assignment i ∷ projectBits rest assignment

projectObservations : List Nat → Cook.Assignment → List (Nat × Bool)
projectObservations [] assignment = []
projectObservations (i ∷ rest) assignment =
  (i , assignment i) ∷ projectObservations rest assignment

pairObservations : List Nat → List Bool → List (Nat × Bool)
pairObservations [] bits = []
pairObservations (i ∷ rest) [] = []
pairObservations (i ∷ rest) (bit ∷ bits) =
  (i , bit) ∷ pairObservations rest bits

pairProjectedBits :
  (indices : List Nat) (assignment : Cook.Assignment) →
  pairObservations indices (projectBits indices assignment)
    ≡ projectObservations indices assignment
pairProjectedBits [] assignment = refl
pairProjectedBits (i ∷ rest) assignment =
  cong ((i , assignment i) ∷_)
    (pairProjectedBits rest assignment)

projectBitsLength :
  (indices : List Nat) (assignment : Cook.Assignment) →
  length (projectBits indices assignment) ≡ length indices
projectBitsLength [] assignment = refl
projectBitsLength (i ∷ rest) assignment =
  cong suc (projectBitsLength rest assignment)

-- The actual finite environment uses first-occurrence lookup.
-- Nat addresses are COMPARED, never enumerated up to maxIndex.
firstLabel : Nat → List (Nat × Bool) → Bool
firstLabel index [] = false
firstLabel index ((seen , bit) ∷ rest)
  with NatP._≟_ index seen
... | yes _ = bit
... | no _ = firstLabel index rest

recoverAssignment : List (Nat × Bool) → Cook.Assignment
recoverAssignment observations index = firstLabel index observations

data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {rest} → value ∈ (value ∷ rest)
  there : ∀ {head rest} → value ∈ rest → value ∈ (head ∷ rest)

memberAppendLeft :
  ∀ {A : Set} {value : A} (xs ys : List A) →
  value ∈ xs → value ∈ (xs ++ ys)
memberAppendLeft [] ys ()
memberAppendLeft (head ∷ tail) ys here = here
memberAppendLeft (head ∷ tail) ys (there m) =
  there (memberAppendLeft tail ys m)

memberAppendRight :
  ∀ {A : Set} {value : A} (xs ys : List A) →
  value ∈ ys → value ∈ (xs ++ ys)
memberAppendRight [] ys m = m
memberAppendRight (head ∷ tail) ys m =
  there (memberAppendRight tail ys m)

data Appears (index : Nat) : Cook.BooleanFormula → Set where
  atVariable : Appears index (Cook.variable index)
  underNegation : ∀ {formula} →
    Appears index formula → Appears index (Cook.negate formula)
  inConjunctionLeft : ∀ {left right} →
    Appears index left → Appears index (Cook.conjunction left right)
  inConjunctionRight : ∀ {left right} →
    Appears index right → Appears index (Cook.conjunction left right)
  inDisjunctionLeft : ∀ {left right} →
    Appears index left → Appears index (Cook.disjunction left right)
  inDisjunctionRight : ∀ {left right} →
    Appears index right → Appears index (Cook.disjunction left right)

appearsInVariableList :
  ∀ {index formula} →
  Appears index formula → index ∈ formulaVariables formula
appearsInVariableList atVariable = here
appearsInVariableList (underNegation m) =
  appearsInVariableList m
appearsInVariableList {formula = Cook.conjunction left right}
  (inConjunctionLeft m) =
  memberAppendLeft (formulaVariables left) (formulaVariables right)
    (appearsInVariableList m)
appearsInVariableList {formula = Cook.conjunction left right}
  (inConjunctionRight m) =
  memberAppendRight (formulaVariables left) (formulaVariables right)
    (appearsInVariableList m)
appearsInVariableList {formula = Cook.disjunction left right}
  (inDisjunctionLeft m) =
  memberAppendLeft (formulaVariables left) (formulaVariables right)
    (appearsInVariableList m)
appearsInVariableList {formula = Cook.disjunction left right}
  (inDisjunctionRight m) =
  memberAppendRight (formulaVariables left) (formulaVariables right)
    (appearsInVariableList m)

-- Every variable appearing in the expression gets exactly its original
-- label from the reconstructed finite observation list.
firstLabelOfProjectedMember :
  (indices : List Nat) (assignment : Cook.Assignment)
  (index : Nat) →
  index ∈ indices →
  firstLabel index (projectObservations indices assignment)
    ≡ assignment index
firstLabelOfProjectedMember [] assignment index ()
firstLabelOfProjectedMember (index ∷ rest) assignment .index here
  with NatP._≟_ index index
... | yes _ = refl
... | no contradiction = ⊥-elim (contradiction refl)
firstLabelOfProjectedMember (head ∷ rest) assignment index
  (there occurrence)
  with NatP._≟_ index head
... | yes equal = cong assignment (sym equal)
... | no _ = firstLabelOfProjectedMember rest assignment index occurrence

projectedEnvironmentAgreesAtOccurrence :
  (formula : Cook.BooleanFormula) (assignment : Cook.Assignment)
  (index : Nat) →
  Appears index formula →
  recoverAssignment
    (projectObservations (formulaVariables formula) assignment)
    index ≡ assignment index
projectedEnvironmentAgreesAtOccurrence formula assignment index appears =
  firstLabelOfProjectedMember (formulaVariables formula)
    assignment index (appearsInVariableList appears)

-- Extensional equality is required ONLY on the indices occurring in
-- this formula, never on all naturals. Boolean evaluation respects it.
evaluateAgreesOnOccurrences :
  (formula : Cook.BooleanFormula)
  (left right : Cook.Assignment) →
  (∀ index → Appears index formula → left index ≡ right index) →
  Cook.evaluate formula left ≡ Cook.evaluate formula right
evaluateAgreesOnOccurrences (Cook.variable index) left right agrees =
  agrees index atVariable
evaluateAgreesOnOccurrences (Cook.constant value) left right agrees =
  refl
evaluateAgreesOnOccurrences (Cook.negate formula) left right agrees =
  cong Cook.notBool
    (evaluateAgreesOnOccurrences formula left right
      (λ index occurrence → agrees index (underNegation occurrence)))
evaluateAgreesOnOccurrences (Cook.conjunction first second)
  left right agrees =
  cong₂ Cook.andBool
    (evaluateAgreesOnOccurrences first left right
      (λ index occurrence →
        agrees index (inConjunctionLeft occurrence)))
    (evaluateAgreesOnOccurrences second left right
      (λ index occurrence →
        agrees index (inConjunctionRight occurrence)))
evaluateAgreesOnOccurrences (Cook.disjunction first second)
  left right agrees =
  cong₂ Cook.orBool
    (evaluateAgreesOnOccurrences first left right
      (λ index occurrence →
        agrees index (inDisjunctionLeft occurrence)))
    (evaluateAgreesOnOccurrences second left right
      (λ index occurrence →
        agrees index (inDisjunctionRight occurrence)))

reconstructedEvaluationEqualsOriginal :
  (formula : Cook.BooleanFormula) (assignment : Cook.Assignment) →
  Cook.evaluate formula
    (recoverAssignment
      (projectObservations (formulaVariables formula) assignment))
  ≡ Cook.evaluate formula assignment
reconstructedEvaluationEqualsOriginal formula assignment =
  evaluateAgreesOnOccurrences formula
    (recoverAssignment
      (projectObservations (formulaVariables formula) assignment))
    assignment
    (projectedEnvironmentAgreesAtOccurrence formula assignment)

-- Use the previously source-written finite same-label checker on Bool,
-- but compare Nat syntax indices instead of N21 finite vertex addresses.
-- This rejects inconsistent REPEATED variable labels.
compatibleCookObservations :
  (Nat × Bool) → (Nat × Bool) → Bool
compatibleCookObservations (index , bit) (other , otherBit)
  with NatP._≟_ index other
... | yes _ = Sparse.boolEqual bit otherBit
... | no _ = true

oneCookObservationAgainst :
  (Nat × Bool) → List (Nat × Bool) → Bool
oneCookObservationAgainst observation [] = true
oneCookObservationAgainst observation (other ∷ rest) =
  Sparse.andBool
    (compatibleCookObservations observation other)
    (oneCookObservationAgainst observation rest)

allCookObservationsConsistent :
  List (Nat × Bool) → Bool
allCookObservationsConsistent [] = true
allCookObservationsConsistent (observation ∷ rest) =
  Sparse.andBool
    (oneCookObservationAgainst observation rest)
    (allCookObservationsConsistent rest)

projectedCookPairCompatible :
  (assignment : Cook.Assignment) (index other : Nat) →
  compatibleCookObservations
    (index , assignment index) (other , assignment other) ≡ true
projectedCookPairCompatible assignment index other
  with NatP._≟_ index other
... | yes refl = Sparse.boolEqualSelf (assignment index)
... | no _ = refl

projectedCookObservationAgainst :
  (assignment : Cook.Assignment) (index : Nat) (indices : List Nat) →
  oneCookObservationAgainst (index , assignment index)
    (projectObservations indices assignment) ≡ true
projectedCookObservationAgainst assignment index [] = refl
projectedCookObservationAgainst assignment index (other ∷ rest)
  rewrite projectedCookPairCompatible assignment index other
        | projectedCookObservationAgainst assignment index rest =
  refl

projectedCookObservationsConsistent :
  (indices : List Nat) (assignment : Cook.Assignment) →
  allCookObservationsConsistent
    (projectObservations indices assignment) ≡ true
projectedCookObservationsConsistent [] assignment = refl
projectedCookObservationsConsistent (index ∷ rest) assignment
  rewrite projectedCookObservationAgainst assignment index rest
        | projectedCookObservationsConsistent rest assignment =
  refl

-- EXACT finite witness: number of Booleans equals number of syntactic
-- variable occurrences, regardless of the magnitudes of their Nat IDs.
CompactCookWitness : Cook.BooleanFormula → Set
CompactCookWitness formula =
  Σ (List Bool) (λ bits →
    (length bits ≡ length (formulaVariables formula))
    × ((allCookObservationsConsistent
          (pairObservations (formulaVariables formula) bits) ≡ true)
    × (Cook.evaluate formula
        (recoverAssignment
          (pairObservations (formulaVariables formula) bits))
        ≡ true)))

cookSatisfiableToCompact :
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula → CompactCookWitness formula
cookSatisfiableToCompact formula
  (Cook.satisfyingAssignment assignment verified) =
  projectBits (formulaVariables formula) assignment ,
  ( projectBitsLength (formulaVariables formula) assignment
  , ( trans
        (cong allCookObservationsConsistent
          (pairProjectedBits (formulaVariables formula) assignment))
        (projectedCookObservationsConsistent
          (formulaVariables formula) assignment)
    , trans
      (cong
        (λ observations →
          Cook.evaluate formula (recoverAssignment observations))
        (pairProjectedBits (formulaVariables formula) assignment))
      (trans
        (reconstructedEvaluationEqualsOriginal formula assignment)
        verified)
    )
  )

compactToCookSatisfiable :
  (formula : Cook.BooleanFormula) →
  CompactCookWitness formula → Cook.Satisfiable formula
compactToCookSatisfiable formula (bits , (size , (consistent , verified))) =
  Cook.satisfyingAssignment
    (recoverAssignment
      (pairObservations (formulaVariables formula) bits))
    verified

cookCompactSatisfiabilityIff :
  (formula : Cook.BooleanFormula) →
  PR.Iff (Cook.Satisfiable formula) (CompactCookWitness formula)
cookCompactSatisfiabilityIff formula =
  PR.iff (cookSatisfiableToCompact formula)
         (compactToCookSatisfiable formula)

-- Tie the finite witness to the K00/N21 shared Boolean Word metric.
-- A bound by the *formula's serialized size* remains a further lemma.
canonicalBitWordIsListLength :
  (bits : List Bool) →
  Word.encodingSize bits ≡ length bits
canonicalBitWordIsListLength [] = refl
canonicalBitWordIsListLength (bit ∷ rest) =
  cong suc (canonicalBitWordIsListLength rest)

compactWitnessExactBitCount :
  (formula : Cook.BooleanFormula)
  (witness : CompactCookWitness formula) →
  Word.encodingSize (proj₁ witness) ≡ length (formulaVariables formula)
compactWitnessExactBitCount formula witness =
  trans (canonicalBitWordIsListLength (proj₁ witness))
        (proj₁ (proj₂ witness))

------------------------------------------------------------------------
-- Quantitative syntax bound: one bit per variable occurrence is no
-- longer than the ACTUAL source-owned unary-prefix Cook token count.
-- In particular a huge Nat variable index does NOT force an
-- exponentially long (maxIndex + 1)-sized satisfying assignment.
-- A 3*token-count SAT word is already serialized by the existing
-- K00 binary codec; the complete bit-machine clock remains open.
------------------------------------------------------------------------

appendNatListLength :
  (xs ys : List Nat) →
  length (xs ++ ys) ≡ length xs + length ys
appendNatListLength [] ys = refl
appendNatListLength (x ∷ rest) ys
  rewrite appendNatListLength rest ys = refl

leqSuccRight :
  ∀ {a b : Nat} → a ≤ b → a ≤ suc b
leqSuccRight z≤n = z≤n
leqSuccRight (s≤s proof) = s≤s (leqSuccRight proof)

variableCountWithinCookTokenCount :
  (formula : Cook.BooleanFormula) →
  length (formulaVariables formula) ≤ Prefix.cookFormulaTokenCount formula
variableCountWithinCookTokenCount (Cook.variable index) = s≤s z≤n
variableCountWithinCookTokenCount (Cook.constant value) = z≤n
variableCountWithinCookTokenCount (Cook.negate formula) =
  leqSuccRight (variableCountWithinCookTokenCount formula)
variableCountWithinCookTokenCount (Cook.conjunction left right)
  rewrite appendNatListLength (formulaVariables left) (formulaVariables right) =
  leqSuccRight
    (NatP.+-mono-≤
      (variableCountWithinCookTokenCount left)
      (variableCountWithinCookTokenCount right))
variableCountWithinCookTokenCount (Cook.disjunction left right)
  rewrite appendNatListLength (formulaVariables left) (formulaVariables right) =
  leqSuccRight
    (NatP.+-mono-≤
      (variableCountWithinCookTokenCount left)
      (variableCountWithinCookTokenCount right))

compactCookCertificateAtMostTokenCount :
  (formula : Cook.BooleanFormula)
  (witness : CompactCookWitness formula) →
  Word.encodingSize (proj₁ witness) ≤ Prefix.cookFormulaTokenCount formula
compactCookCertificateAtMostTokenCount formula witness
  rewrite compactWitnessExactBitCount formula witness =
  variableCountWithinCookTokenCount formula
