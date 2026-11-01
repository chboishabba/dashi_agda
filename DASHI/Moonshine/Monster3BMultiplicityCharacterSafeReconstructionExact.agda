module DASHI.Moonshine.Monster3BMultiplicityCharacterSafeReconstructionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Make the classwise character calculation fail closed over an arbitrary
-- trace algebra, including cyclotomic character values.  Pointwise division by
-- the Heisenberg trace is admitted only on classes carrying an explicit product
-- equation.  Vanishing-trace classes must instead be reconstructed from an
-- independent class relation or inner-product calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

------------------------------------------------------------------------
-- Minimal trace algebra.  No order or division is assumed.
------------------------------------------------------------------------

record TraceAlgebra : Set₁ where
  field
    Carrier : Set
    zero : Carrier
    add : Carrier → Carrier → Carrier
    multiply : Carrier → Carrier → Carrier
    zeroMultiplyLeft : (value : Carrier) → multiply zero value ≡ zero

open TraceAlgebra public

------------------------------------------------------------------------
-- Two legitimate recovery methods.
------------------------------------------------------------------------

data RecoveryKind : Set where
  quotientOnNonzeroTrace : RecoveryKind
  independentClassEquation : RecoveryKind

record MultiplicityClassRow (algebra : TraceAlgebra) : Set where
  constructor multiplicity-class-row
  field
    ambientTrace : Carrier algebra
    heisenbergTrace : Carrier algebra
    multiplicityTrace : Carrier algebra
    recoveryKind : RecoveryKind

    quotientEquation :
      recoveryKind ≡ quotientOnNonzeroTrace →
      multiply algebra heisenbergTrace multiplicityTrace ≡ ambientTrace

    independentEquation :
      recoveryKind ≡ independentClassEquation →
      ambientTrace ≡ multiply algebra heisenbergTrace multiplicityTrace

open MultiplicityClassRow public

quotientRow :
  (algebra : TraceAlgebra) →
  (ambient heisenberg multiplicity : Carrier algebra) →
  multiply algebra heisenberg multiplicity ≡ ambient →
  MultiplicityClassRow algebra
quotientRow algebra ambient heisenberg multiplicity equation =
  multiplicity-class-row
    ambient heisenberg multiplicity quotientOnNonzeroTrace
    (λ _ → equation)
    (λ ())

independentRow :
  (algebra : TraceAlgebra) →
  (ambient heisenberg multiplicity : Carrier algebra) →
  ambient ≡ multiply algebra heisenberg multiplicity →
  MultiplicityClassRow algebra
independentRow algebra ambient heisenberg multiplicity equation =
  multiplicity-class-row
    ambient heisenberg multiplicity independentClassEquation
    (λ ())
    (λ _ → equation)

classRowReconstructsAmbient :
  (algebra : TraceAlgebra) →
  (row : MultiplicityClassRow algebra) →
  multiply algebra (heisenbergTrace row) (multiplicityTrace row)
  ≡ ambientTrace row
classRowReconstructsAmbient algebra row with recoveryKind row
... | quotientOnNonzeroTrace = quotientEquation row refl
... | independentClassEquation = sym (independentEquation row refl)

------------------------------------------------------------------------
-- Finite class-table reconstruction.
------------------------------------------------------------------------

sumAmbient :
  (algebra : TraceAlgebra) →
  List (MultiplicityClassRow algebra) →
  Carrier algebra
sumAmbient algebra [] = zero algebra
sumAmbient algebra (row ∷ rows) =
  add algebra (ambientTrace row) (sumAmbient algebra rows)

sumTensorTrace :
  (algebra : TraceAlgebra) →
  List (MultiplicityClassRow algebra) →
  Carrier algebra
sumTensorTrace algebra [] = zero algebra
sumTensorTrace algebra (row ∷ rows) =
  add algebra
    (multiply algebra (heisenbergTrace row) (multiplicityTrace row))
    (sumTensorTrace algebra rows)

multiplicityCharacterReconstructsAllClasses :
  (algebra : TraceAlgebra) →
  (rows : List (MultiplicityClassRow algebra)) →
  sumTensorTrace algebra rows ≡ sumAmbient algebra rows
multiplicityCharacterReconstructsAllClasses algebra [] = refl
multiplicityCharacterReconstructsAllClasses algebra (row ∷ rows) =
  cong₂
    (add algebra)
    (classRowReconstructsAmbient algebra row)
    (multiplicityCharacterReconstructsAllClasses algebra rows)

------------------------------------------------------------------------
-- The zero-trace boundary.
------------------------------------------------------------------------

record ZeroTraceClassObligation (algebra : TraceAlgebra) : Set where
  constructor zero-trace-class-obligation
  field
    ambientTraceAtClass : Carrier algebra
    multiplicityTraceAtClass : Carrier algebra
    heisenbergTraceAtClass : Carrier algebra
    heisenbergTraceAtClassIsZero :
      heisenbergTraceAtClass ≡ zero algebra
    independentRecovery :
      ambientTraceAtClass
      ≡ multiply algebra heisenbergTraceAtClass multiplicityTraceAtClass

open ZeroTraceClassObligation public

zeroTraceClassCannotUseQuotientAlone :
  (algebra : TraceAlgebra) →
  (obligation : ZeroTraceClassObligation algebra) →
  ambientTraceAtClass obligation ≡ zero algebra
zeroTraceClassCannotUseQuotientAlone algebra obligation =
  trans
    (independentRecovery obligation)
    (trans
      (cong₂
        (multiply algebra)
        (heisenbergTraceAtClassIsZero obligation)
        refl)
      (zeroMultiplyLeft algebra (multiplicityTraceAtClass obligation)))

------------------------------------------------------------------------
-- Actual 12 + 78 certification surface.
------------------------------------------------------------------------

record ActualMultiplicityCharacterCertificate
  (algebra : TraceAlgebra) : Set₁ where
  field
    InertiaClass : Set
    classRows : List (MultiplicityClassRow algebra)
    twelveCharacter : InertiaClass → Carrier algebra
    seventyEightCharacter : InertiaClass → Carrier algebra
    actualMultiplicityCharacter : InertiaClass → Carrier algebra

    classwiseTwelvePlusSeventyEight :
      (class : InertiaClass) →
      actualMultiplicityCharacter class
      ≡ add algebra
          (twelveCharacter class)
          (seventyEightCharacter class)

open ActualMultiplicityCharacterCertificate public

multiplicityCharacterEqualsTwelvePlusSeventyEight :
  (algebra : TraceAlgebra) →
  (certificate : ActualMultiplicityCharacterCertificate algebra) →
  (class : InertiaClass certificate) →
  actualMultiplicityCharacter certificate class
  ≡ add algebra
      (twelveCharacter certificate class)
      (seventyEightCharacter certificate class)
multiplicityCharacterEqualsTwelvePlusSeventyEight algebra =
  classwiseTwelvePlusSeventyEight

------------------------------------------------------------------------
-- A small natural-number instance used only for finite regression examples.
-- The actual inertia character will use its cyclotomic trace algebra.
------------------------------------------------------------------------

naturalTraceAlgebra : TraceAlgebra
naturalTraceAlgebra = record
  { Carrier = Nat
  ; zero = 0
  ; add = _+_
  ; multiply = _*_
  ; zeroMultiplyLeft = λ _ → refl
  }
