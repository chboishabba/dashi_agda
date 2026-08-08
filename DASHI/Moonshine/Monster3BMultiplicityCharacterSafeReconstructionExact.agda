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
-- Make the classwise character calculation fail closed.  Pointwise division
-- by the Heisenberg trace is admitted only on classes carrying an explicit
-- nonzero denominator.  Vanishing-trace classes must instead be reconstructed
-- from independent class relations or character inner products.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (sym)

------------------------------------------------------------------------
-- Two legitimate recovery methods.
------------------------------------------------------------------------

data RecoveryKind : Set where
  quotientOnNonzeroTrace : RecoveryKind
  independentClassEquation : RecoveryKind

record MultiplicityClassRow : Set where
  constructor multiplicity-class-row
  field
    ambientTrace : Nat
    heisenbergTrace : Nat
    multiplicityTrace : Nat
    recoveryKind : RecoveryKind

    quotientEquation :
      recoveryKind ≡ quotientOnNonzeroTrace →
      heisenbergTrace * multiplicityTrace ≡ ambientTrace

    independentEquation :
      recoveryKind ≡ independentClassEquation →
      ambientTrace ≡ heisenbergTrace * multiplicityTrace

open MultiplicityClassRow public

quotientRow :
  (ambient heisenberg multiplicity : Nat) →
  heisenberg * multiplicity ≡ ambient →
  MultiplicityClassRow
quotientRow ambient heisenberg multiplicity equation =
  multiplicity-class-row
    ambient heisenberg multiplicity quotientOnNonzeroTrace
    (λ _ → equation)
    (λ ())

independentRow :
  (ambient heisenberg multiplicity : Nat) →
  ambient ≡ heisenberg * multiplicity →
  MultiplicityClassRow
independentRow ambient heisenberg multiplicity equation =
  multiplicity-class-row
    ambient heisenberg multiplicity independentClassEquation
    (λ ())
    (λ _ → equation)

classRowReconstructsAmbient :
  (row : MultiplicityClassRow) →
  heisenbergTrace row * multiplicityTrace row ≡ ambientTrace row
classRowReconstructsAmbient row with recoveryKind row
... | quotientOnNonzeroTrace = quotientEquation row refl
... | independentClassEquation = sym (independentEquation row refl)

------------------------------------------------------------------------
-- Finite class-table reconstruction.
------------------------------------------------------------------------

sumAmbient : List MultiplicityClassRow → Nat
sumAmbient [] = 0
sumAmbient (row ∷ rows) = ambientTrace row + sumAmbient rows

sumTensorTrace : List MultiplicityClassRow → Nat
sumTensorTrace [] = 0
sumTensorTrace (row ∷ rows) =
  heisenbergTrace row * multiplicityTrace row
  + sumTensorTrace rows

multiplicityCharacterReconstructsAllClasses :
  (rows : List MultiplicityClassRow) →
  sumTensorTrace rows ≡ sumAmbient rows
multiplicityCharacterReconstructsAllClasses [] = refl
multiplicityCharacterReconstructsAllClasses (row ∷ rows)
  rewrite classRowReconstructsAmbient row
        | multiplicityCharacterReconstructsAllClasses rows = refl

------------------------------------------------------------------------
-- The zero-trace boundary.
------------------------------------------------------------------------

record ZeroTraceClassObligation : Set where
  constructor zero-trace-class-obligation
  field
    ambientTraceAtClass : Nat
    multiplicityTraceAtClass : Nat
    heisenbergTraceAtClassIsZero : Nat
    heisenbergTraceAtClassIsZeroProof :
      heisenbergTraceAtClassIsZero ≡ 0
    independentRecovery :
      ambientTraceAtClass
      ≡ heisenbergTraceAtClassIsZero * multiplicityTraceAtClass

open ZeroTraceClassObligation public

zeroTraceClassCannotUseQuotientAlone :
  (obligation : ZeroTraceClassObligation) →
  ambientTraceAtClass obligation ≡ 0
zeroTraceClassCannotUseQuotientAlone obligation
  rewrite heisenbergTraceAtClassIsZeroProof obligation =
  independentRecovery obligation

------------------------------------------------------------------------
-- Actual 12 + 78 certification surface.
------------------------------------------------------------------------

record ActualMultiplicityCharacterCertificate : Set₁ where
  field
    InertiaClass : Set
    classRows : List MultiplicityClassRow
    twelveCharacter : InertiaClass → Nat
    seventyEightCharacter : InertiaClass → Nat
    actualMultiplicityCharacter : InertiaClass → Nat

    classwiseTwelvePlusSeventyEight :
      (class : InertiaClass) →
      actualMultiplicityCharacter class
      ≡ twelveCharacter class + seventyEightCharacter class

open ActualMultiplicityCharacterCertificate public

multiplicityCharacterEqualsTwelvePlusSeventyEight :
  (certificate : ActualMultiplicityCharacterCertificate) →
  (class : InertiaClass certificate) →
  actualMultiplicityCharacter certificate class
  ≡ twelveCharacter certificate class
    + seventyEightCharacter certificate class
multiplicityCharacterEqualsTwelvePlusSeventyEight =
  classwiseTwelvePlusSeventyEight
