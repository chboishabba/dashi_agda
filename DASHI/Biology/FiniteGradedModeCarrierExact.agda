module DASHI.Biology.FiniteGradedModeCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- DASHI CONTRIBUTION
-- Encode the homogeneous mode grading rule division-free.  For homogeneous
-- weights r and s, a mode index m and output weight t, the usual equation
--
--   t = r + s - m - 1
--
-- is represented without truncated subtraction as
--
--   t + m + 1 = r + s.
--
-- The weight-two first product is then checked exactly:
-- 2 + 1 + 1 = 2 + 2, hence u_1 v again has weight two.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

data Grade012 : Set where
  gradeZero : Grade012
  gradeOne : Grade012
  gradeTwo : Grade012

gradeValue : Grade012 → Nat
gradeValue gradeZero = 0
gradeValue gradeOne = 1
gradeValue gradeTwo = 2

record ModeGradeCertificate : Set where
  constructor modeGradeCertificate
  field
    leftWeight : Nat
    rightWeight : Nat
    modeIndex : Nat
    outputWeight : Nat
    gradeBalance :
      outputWeight + modeIndex + 1
      ≡ leftWeight + rightWeight

open ModeGradeCertificate public

weightTwoFirstModeClosure : ModeGradeCertificate
weightTwoFirstModeClosure =
  modeGradeCertificate 2 2 1 2 refl

weightTwoFirstModeOutputIsTwo :
  outputWeight weightTwoFirstModeClosure ≡ 2
weightTwoFirstModeOutputIsTwo = refl

data ModeIndexStatus : Set where
  nonnegativeModeRepresented : ModeIndexStatus
  negativeModeRequiresIntegerCarrier : ModeIndexStatus

firstProductModeStatus : ModeIndexStatus
firstProductModeStatus = nonnegativeModeRepresented

-- The genuine vacuum creation mode is indexed by -1.  It is deliberately not
-- encoded by pretending that a natural-number mode has the same grade law.
vacuumCreationModeStatus : ModeIndexStatus
vacuumCreationModeStatus = negativeModeRequiresIntegerCarrier

data VOAAxiomStatus : Set where
  finiteGradeArithmeticChecked : VOAAxiomStatus
  localityWitnessRequired : VOAAxiomStatus
  jacobiWitnessRequired : VOAAxiomStatus
  vacuumFieldWitnessRequired : VOAAxiomStatus
  translationWitnessRequired : VOAAxiomStatus

weightTwoClosureStatus : VOAAxiomStatus
weightTwoClosureStatus = finiteGradeArithmeticChecked

localityStatus : VOAAxiomStatus
localityStatus = localityWitnessRequired

jacobiStatus : VOAAxiomStatus
jacobiStatus = jacobiWitnessRequired

record FiniteModeBoundary : Set where
  constructor finiteModeBoundary
  field
    gradeArithmeticConstructsStateFieldCorrespondence : Set
    gradeArithmeticDoesNotConstructStateFieldCorrespondence :
      gradeArithmeticConstructsStateFieldCorrespondence → Set

    gradeArithmeticProvesJacobiIdentity : Set
    gradeArithmeticDoesNotProveJacobiIdentity :
      gradeArithmeticProvesJacobiIdentity → Set

canonicalFiniteModeBoundary : FiniteModeBoundary
canonicalFiniteModeBoundary =
  finiteModeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
