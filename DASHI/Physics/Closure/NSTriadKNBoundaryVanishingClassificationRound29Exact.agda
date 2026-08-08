module DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The one external boundary owner is internally partitioned by the reason an
-- atom disappears: exact absence, fixed-cutoff finite support, geometric tail,
-- strong convergence, or dominated convergence. The signed total is proved to
-- be the sum of these five subledgers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

data BoundaryVanishingReason : Set where
  exactAbsence : BoundaryVanishingReason
  fixedCutoffFiniteSupport : BoundaryVanishingReason
  geometricTail : BoundaryVanishingReason
  strongConvergence : BoundaryVanishingReason
  dominatedConvergence : BoundaryVanishingReason

record BoundaryAtom : Set where
  constructor boundary-atom
  field
    signedValue : ℚ
    vanishingReason : BoundaryVanishingReason

open BoundaryAtom public

boundaryTotal : List BoundaryAtom → ℚ
boundaryTotal [] = 0ℚ
boundaryTotal (atom ∷ rest) = signedValue atom + boundaryTotal rest

reasonTotal : BoundaryVanishingReason → List BoundaryAtom → ℚ
reasonTotal reason [] = 0ℚ
reasonTotal reason (boundary-atom value exactAbsence ∷ rest) with reason
... | exactAbsence = value + reasonTotal exactAbsence rest
... | fixedCutoffFiniteSupport = reasonTotal fixedCutoffFiniteSupport rest
... | geometricTail = reasonTotal geometricTail rest
... | strongConvergence = reasonTotal strongConvergence rest
... | dominatedConvergence = reasonTotal dominatedConvergence rest
reasonTotal reason (boundary-atom value fixedCutoffFiniteSupport ∷ rest) with reason
... | exactAbsence = reasonTotal exactAbsence rest
... | fixedCutoffFiniteSupport = value + reasonTotal fixedCutoffFiniteSupport rest
... | geometricTail = reasonTotal geometricTail rest
... | strongConvergence = reasonTotal strongConvergence rest
... | dominatedConvergence = reasonTotal dominatedConvergence rest
reasonTotal reason (boundary-atom value geometricTail ∷ rest) with reason
... | exactAbsence = reasonTotal exactAbsence rest
... | fixedCutoffFiniteSupport = reasonTotal fixedCutoffFiniteSupport rest
... | geometricTail = value + reasonTotal geometricTail rest
... | strongConvergence = reasonTotal strongConvergence rest
... | dominatedConvergence = reasonTotal dominatedConvergence rest
reasonTotal reason (boundary-atom value strongConvergence ∷ rest) with reason
... | exactAbsence = reasonTotal exactAbsence rest
... | fixedCutoffFiniteSupport = reasonTotal fixedCutoffFiniteSupport rest
... | geometricTail = reasonTotal geometricTail rest
... | strongConvergence = value + reasonTotal strongConvergence rest
... | dominatedConvergence = reasonTotal dominatedConvergence rest
reasonTotal reason (boundary-atom value dominatedConvergence ∷ rest) with reason
... | exactAbsence = reasonTotal exactAbsence rest
... | fixedCutoffFiniteSupport = reasonTotal fixedCutoffFiniteSupport rest
... | geometricTail = reasonTotal geometricTail rest
... | strongConvergence = reasonTotal strongConvergence rest
... | dominatedConvergence = value + reasonTotal dominatedConvergence rest

boundaryReasonPartitionExact :
  (atoms : List BoundaryAtom) →
  boundaryTotal atoms
  ≡ reasonTotal exactAbsence atoms
    + reasonTotal fixedCutoffFiniteSupport atoms
    + reasonTotal geometricTail atoms
    + reasonTotal strongConvergence atoms
    + reasonTotal dominatedConvergence atoms
boundaryReasonPartitionExact [] = solve []
boundaryReasonPartitionExact (boundary-atom value exactAbsence ∷ rest) =
  trans
    (cong (value +_) (boundaryReasonPartitionExact rest))
    (solve
      ( value
      ∷ reasonTotal exactAbsence rest
      ∷ reasonTotal fixedCutoffFiniteSupport rest
      ∷ reasonTotal geometricTail rest
      ∷ reasonTotal strongConvergence rest
      ∷ reasonTotal dominatedConvergence rest
      ∷ []))
boundaryReasonPartitionExact
  (boundary-atom value fixedCutoffFiniteSupport ∷ rest) =
  trans
    (cong (value +_) (boundaryReasonPartitionExact rest))
    (solve
      ( value
      ∷ reasonTotal exactAbsence rest
      ∷ reasonTotal fixedCutoffFiniteSupport rest
      ∷ reasonTotal geometricTail rest
      ∷ reasonTotal strongConvergence rest
      ∷ reasonTotal dominatedConvergence rest
      ∷ []))
boundaryReasonPartitionExact (boundary-atom value geometricTail ∷ rest) =
  trans
    (cong (value +_) (boundaryReasonPartitionExact rest))
    (solve
      ( value
      ∷ reasonTotal exactAbsence rest
      ∷ reasonTotal fixedCutoffFiniteSupport rest
      ∷ reasonTotal geometricTail rest
      ∷ reasonTotal strongConvergence rest
      ∷ reasonTotal dominatedConvergence rest
      ∷ []))
boundaryReasonPartitionExact (boundary-atom value strongConvergence ∷ rest) =
  trans
    (cong (value +_) (boundaryReasonPartitionExact rest))
    (solve
      ( value
      ∷ reasonTotal exactAbsence rest
      ∷ reasonTotal fixedCutoffFiniteSupport rest
      ∷ reasonTotal geometricTail rest
      ∷ reasonTotal strongConvergence rest
      ∷ reasonTotal dominatedConvergence rest
      ∷ []))
boundaryReasonPartitionExact (boundary-atom value dominatedConvergence ∷ rest) =
  trans
    (cong (value +_) (boundaryReasonPartitionExact rest))
    (solve
      ( value
      ∷ reasonTotal exactAbsence rest
      ∷ reasonTotal fixedCutoffFiniteSupport rest
      ∷ reasonTotal geometricTail rest
      ∷ reasonTotal strongConvergence rest
      ∷ reasonTotal dominatedConvergence rest
      ∷ []))

record AllBoundarySubtypesVanish (atoms : List BoundaryAtom) : Set where
  constructor all-boundary-subtypes-vanish
  field
    exactAbsenceVanishes : reasonTotal exactAbsence atoms ≡ 0ℚ
    fixedSupportVanishes :
      reasonTotal fixedCutoffFiniteSupport atoms ≡ 0ℚ
    geometricTailVanishes : reasonTotal geometricTail atoms ≡ 0ℚ
    strongConvergenceVanishes :
      reasonTotal strongConvergence atoms ≡ 0ℚ
    dominatedConvergenceVanishes :
      reasonTotal dominatedConvergence atoms ≡ 0ℚ

open AllBoundarySubtypesVanish public

classifiedBoundaryTotalVanishes :
  (atoms : List BoundaryAtom) →
  AllBoundarySubtypesVanish atoms →
  boundaryTotal atoms ≡ 0ℚ
classifiedBoundaryTotalVanishes atoms evidence
  rewrite boundaryReasonPartitionExact atoms
        | exactAbsenceVanishes evidence
        | fixedSupportVanishes evidence
        | geometricTailVanishes evidence
        | strongConvergenceVanishes evidence
        | dominatedConvergenceVanishes evidence = solve []

boundaryVanishingClassificationClosed : Bool
boundaryVanishingClassificationClosed = true

physicalBoundarySubtypeLimitsClosed : Bool
physicalBoundarySubtypeLimitsClosed = false

boundaryVanishingClassificationClosedIsTrue :
  boundaryVanishingClassificationClosed ≡ true
boundaryVanishingClassificationClosedIsTrue = refl
