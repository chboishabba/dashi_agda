module DASHI.Physics.Closure.NSTriadKNBoundaryLiteralZeroAtomsRound55Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The boundary ledger stores the signed LIMIT contribution of each classified
-- atom.  Therefore once the literal PDE construction has evaluated every such
-- atom to zero, the five reason totals are not additional analytic hypotheses:
-- they follow by structural recursion.  This file proves that recursion and
-- constructs the Round-47 FivePhysicalBoundaryLocalLimits certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNBoundaryFiveLocalLimitsRound47Exact as Five

record LiteralZeroBoundaryAtom : Set where
  constructor literal-zero-boundary-atom
  field
    atom : Boundary.BoundaryAtom
    literalLimitIsZero : Boundary.signedValue atom ≡ 0ℚ

open LiteralZeroBoundaryAtom public

forgetZeroAtoms : List LiteralZeroBoundaryAtom → List Boundary.BoundaryAtom
forgetZeroAtoms [] = []
forgetZeroAtoms (entry ∷ rest) = atom entry ∷ forgetZeroAtoms rest

reasonTotalZero :
  (reason : Boundary.BoundaryVanishingReason) →
  (entries : List LiteralZeroBoundaryAtom) →
  Boundary.reasonTotal reason (forgetZeroAtoms entries) ≡ 0ℚ
reasonTotalZero reason [] = refl
reasonTotalZero reason (literal-zero-boundary-atom
  (Boundary.boundary-atom value Boundary.exactAbsence) valueZero ∷ rest)
  with reason
... | Boundary.exactAbsence rewrite valueZero | reasonTotalZero Boundary.exactAbsence rest = refl
... | Boundary.fixedCutoffFiniteSupport = reasonTotalZero Boundary.fixedCutoffFiniteSupport rest
... | Boundary.geometricTail = reasonTotalZero Boundary.geometricTail rest
... | Boundary.strongConvergence = reasonTotalZero Boundary.strongConvergence rest
... | Boundary.dominatedConvergence = reasonTotalZero Boundary.dominatedConvergence rest
reasonTotalZero reason (literal-zero-boundary-atom
  (Boundary.boundary-atom value Boundary.fixedCutoffFiniteSupport) valueZero ∷ rest)
  with reason
... | Boundary.exactAbsence = reasonTotalZero Boundary.exactAbsence rest
... | Boundary.fixedCutoffFiniteSupport rewrite valueZero | reasonTotalZero Boundary.fixedCutoffFiniteSupport rest = refl
... | Boundary.geometricTail = reasonTotalZero Boundary.geometricTail rest
... | Boundary.strongConvergence = reasonTotalZero Boundary.strongConvergence rest
... | Boundary.dominatedConvergence = reasonTotalZero Boundary.dominatedConvergence rest
reasonTotalZero reason (literal-zero-boundary-atom
  (Boundary.boundary-atom value Boundary.geometricTail) valueZero ∷ rest)
  with reason
... | Boundary.exactAbsence = reasonTotalZero Boundary.exactAbsence rest
... | Boundary.fixedCutoffFiniteSupport = reasonTotalZero Boundary.fixedCutoffFiniteSupport rest
... | Boundary.geometricTail rewrite valueZero | reasonTotalZero Boundary.geometricTail rest = refl
... | Boundary.strongConvergence = reasonTotalZero Boundary.strongConvergence rest
... | Boundary.dominatedConvergence = reasonTotalZero Boundary.dominatedConvergence rest
reasonTotalZero reason (literal-zero-boundary-atom
  (Boundary.boundary-atom value Boundary.strongConvergence) valueZero ∷ rest)
  with reason
... | Boundary.exactAbsence = reasonTotalZero Boundary.exactAbsence rest
... | Boundary.fixedCutoffFiniteSupport = reasonTotalZero Boundary.fixedCutoffFiniteSupport rest
... | Boundary.geometricTail = reasonTotalZero Boundary.geometricTail rest
... | Boundary.strongConvergence rewrite valueZero | reasonTotalZero Boundary.strongConvergence rest = refl
... | Boundary.dominatedConvergence = reasonTotalZero Boundary.dominatedConvergence rest
reasonTotalZero reason (literal-zero-boundary-atom
  (Boundary.boundary-atom value Boundary.dominatedConvergence) valueZero ∷ rest)
  with reason
... | Boundary.exactAbsence = reasonTotalZero Boundary.exactAbsence rest
... | Boundary.fixedCutoffFiniteSupport = reasonTotalZero Boundary.fixedCutoffFiniteSupport rest
... | Boundary.geometricTail = reasonTotalZero Boundary.geometricTail rest
... | Boundary.strongConvergence = reasonTotalZero Boundary.strongConvergence rest
... | Boundary.dominatedConvergence rewrite valueZero | reasonTotalZero Boundary.dominatedConvergence rest = refl

literalZeroAtomsToFiveLimits :
  (entries : List LiteralZeroBoundaryAtom) →
  Five.FivePhysicalBoundaryLocalLimits (forgetZeroAtoms entries)
literalZeroAtomsToFiveLimits entries = record
  { physicalExactAbsenceLimit = reasonTotalZero Boundary.exactAbsence entries
  ; physicalFixedCutoffFiniteSupportLimit = reasonTotalZero Boundary.fixedCutoffFiniteSupport entries
  ; physicalGeometricTailLimit = reasonTotalZero Boundary.geometricTail entries
  ; physicalStrongConvergenceLimit = reasonTotalZero Boundary.strongConvergence entries
  ; physicalDominatedConvergenceLimit = reasonTotalZero Boundary.dominatedConvergence entries
  }

boundaryFiveLimitsDerivedFromLiteralAtoms : Bool
boundaryFiveLimitsDerivedFromLiteralAtoms = true

boundaryFiveLimitsDerivedFromLiteralAtomsIsTrue :
  boundaryFiveLimitsDerivedFromLiteralAtoms ≡ true
boundaryFiveLimitsDerivedFromLiteralAtomsIsTrue = refl
