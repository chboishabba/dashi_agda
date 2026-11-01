module DASHI.Physics.Closure.NSTriadKNBoundaryDefinitionalVanishRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Some periodic boundary subtypes need no analytic limit at all.  If the
-- classified atom ledger contains no atom of a given vanishing reason, its
-- reason-total is definitionally/combinatorially zero.  This file proves that
-- statement once for all five reasons.  The physical periodic-torus lane may
-- therefore discharge exact absence, and any eventually-empty finite-support
-- subtype, by constructing NoReason rather than invoking convergence theory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary

data ReasonDifferent :
    Boundary.BoundaryVanishingReason →
    Boundary.BoundaryVanishingReason → Set where
  exact-vs-fixed : ReasonDifferent Boundary.exactAbsence Boundary.fixedCutoffFiniteSupport
  exact-vs-geometric : ReasonDifferent Boundary.exactAbsence Boundary.geometricTail
  exact-vs-strong : ReasonDifferent Boundary.exactAbsence Boundary.strongConvergence
  exact-vs-dominated : ReasonDifferent Boundary.exactAbsence Boundary.dominatedConvergence
  fixed-vs-exact : ReasonDifferent Boundary.fixedCutoffFiniteSupport Boundary.exactAbsence
  fixed-vs-geometric : ReasonDifferent Boundary.fixedCutoffFiniteSupport Boundary.geometricTail
  fixed-vs-strong : ReasonDifferent Boundary.fixedCutoffFiniteSupport Boundary.strongConvergence
  fixed-vs-dominated : ReasonDifferent Boundary.fixedCutoffFiniteSupport Boundary.dominatedConvergence
  geometric-vs-exact : ReasonDifferent Boundary.geometricTail Boundary.exactAbsence
  geometric-vs-fixed : ReasonDifferent Boundary.geometricTail Boundary.fixedCutoffFiniteSupport
  geometric-vs-strong : ReasonDifferent Boundary.geometricTail Boundary.strongConvergence
  geometric-vs-dominated : ReasonDifferent Boundary.geometricTail Boundary.dominatedConvergence
  strong-vs-exact : ReasonDifferent Boundary.strongConvergence Boundary.exactAbsence
  strong-vs-fixed : ReasonDifferent Boundary.strongConvergence Boundary.fixedCutoffFiniteSupport
  strong-vs-geometric : ReasonDifferent Boundary.strongConvergence Boundary.geometricTail
  strong-vs-dominated : ReasonDifferent Boundary.strongConvergence Boundary.dominatedConvergence
  dominated-vs-exact : ReasonDifferent Boundary.dominatedConvergence Boundary.exactAbsence
  dominated-vs-fixed : ReasonDifferent Boundary.dominatedConvergence Boundary.fixedCutoffFiniteSupport
  dominated-vs-geometric : ReasonDifferent Boundary.dominatedConvergence Boundary.geometricTail
  dominated-vs-strong : ReasonDifferent Boundary.dominatedConvergence Boundary.strongConvergence

reasonIrreflexive :
  ∀ {reason} → ReasonDifferent reason reason → ⊥
reasonIrreflexive ()

data NoReason
    (reason : Boundary.BoundaryVanishingReason) :
    List Boundary.BoundaryAtom → Set where
  noReasonNil : NoReason reason []
  noReasonCons :
    ∀ {value atomReason rest} →
    ReasonDifferent reason atomReason →
    NoReason reason rest →
    NoReason reason (Boundary.boundary-atom value atomReason ∷ rest)

reasonTotalZeroWhenAbsent :
  ∀ reason atoms →
  NoReason reason atoms →
  Boundary.reasonTotal reason atoms ≡ 0ℚ
reasonTotalZeroWhenAbsent reason [] noReasonNil = refl
reasonTotalZeroWhenAbsent
    Boundary.exactAbsence
    (Boundary.boundary-atom value Boundary.fixedCutoffFiniteSupport ∷ rest)
    (noReasonCons exact-vs-fixed tail) =
  reasonTotalZeroWhenAbsent Boundary.exactAbsence rest tail
reasonTotalZeroWhenAbsent
    Boundary.exactAbsence
    (Boundary.boundary-atom value Boundary.geometricTail ∷ rest)
    (noReasonCons exact-vs-geometric tail) =
  reasonTotalZeroWhenAbsent Boundary.exactAbsence rest tail
reasonTotalZeroWhenAbsent
    Boundary.exactAbsence
    (Boundary.boundary-atom value Boundary.strongConvergence ∷ rest)
    (noReasonCons exact-vs-strong tail) =
  reasonTotalZeroWhenAbsent Boundary.exactAbsence rest tail
reasonTotalZeroWhenAbsent
    Boundary.exactAbsence
    (Boundary.boundary-atom value Boundary.dominatedConvergence ∷ rest)
    (noReasonCons exact-vs-dominated tail) =
  reasonTotalZeroWhenAbsent Boundary.exactAbsence rest tail
reasonTotalZeroWhenAbsent
    Boundary.fixedCutoffFiniteSupport
    (Boundary.boundary-atom value Boundary.exactAbsence ∷ rest)
    (noReasonCons fixed-vs-exact tail) =
  reasonTotalZeroWhenAbsent Boundary.fixedCutoffFiniteSupport rest tail
reasonTotalZeroWhenAbsent
    Boundary.fixedCutoffFiniteSupport
    (Boundary.boundary-atom value Boundary.geometricTail ∷ rest)
    (noReasonCons fixed-vs-geometric tail) =
  reasonTotalZeroWhenAbsent Boundary.fixedCutoffFiniteSupport rest tail
reasonTotalZeroWhenAbsent
    Boundary.fixedCutoffFiniteSupport
    (Boundary.boundary-atom value Boundary.strongConvergence ∷ rest)
    (noReasonCons fixed-vs-strong tail) =
  reasonTotalZeroWhenAbsent Boundary.fixedCutoffFiniteSupport rest tail
reasonTotalZeroWhenAbsent
    Boundary.fixedCutoffFiniteSupport
    (Boundary.boundary-atom value Boundary.dominatedConvergence ∷ rest)
    (noReasonCons fixed-vs-dominated tail) =
  reasonTotalZeroWhenAbsent Boundary.fixedCutoffFiniteSupport rest tail
reasonTotalZeroWhenAbsent
    Boundary.geometricTail
    (Boundary.boundary-atom value Boundary.exactAbsence ∷ rest)
    (noReasonCons geometric-vs-exact tail) =
  reasonTotalZeroWhenAbsent Boundary.geometricTail rest tail
reasonTotalZeroWhenAbsent
    Boundary.geometricTail
    (Boundary.boundary-atom value Boundary.fixedCutoffFiniteSupport ∷ rest)
    (noReasonCons geometric-vs-fixed tail) =
  reasonTotalZeroWhenAbsent Boundary.geometricTail rest tail
reasonTotalZeroWhenAbsent
    Boundary.geometricTail
    (Boundary.boundary-atom value Boundary.strongConvergence ∷ rest)
    (noReasonCons geometric-vs-strong tail) =
  reasonTotalZeroWhenAbsent Boundary.geometricTail rest tail
reasonTotalZeroWhenAbsent
    Boundary.geometricTail
    (Boundary.boundary-atom value Boundary.dominatedConvergence ∷ rest)
    (noReasonCons geometric-vs-dominated tail) =
  reasonTotalZeroWhenAbsent Boundary.geometricTail rest tail
reasonTotalZeroWhenAbsent
    Boundary.strongConvergence
    (Boundary.boundary-atom value Boundary.exactAbsence ∷ rest)
    (noReasonCons strong-vs-exact tail) =
  reasonTotalZeroWhenAbsent Boundary.strongConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.strongConvergence
    (Boundary.boundary-atom value Boundary.fixedCutoffFiniteSupport ∷ rest)
    (noReasonCons strong-vs-fixed tail) =
  reasonTotalZeroWhenAbsent Boundary.strongConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.strongConvergence
    (Boundary.boundary-atom value Boundary.geometricTail ∷ rest)
    (noReasonCons strong-vs-geometric tail) =
  reasonTotalZeroWhenAbsent Boundary.strongConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.strongConvergence
    (Boundary.boundary-atom value Boundary.dominatedConvergence ∷ rest)
    (noReasonCons strong-vs-dominated tail) =
  reasonTotalZeroWhenAbsent Boundary.strongConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.dominatedConvergence
    (Boundary.boundary-atom value Boundary.exactAbsence ∷ rest)
    (noReasonCons dominated-vs-exact tail) =
  reasonTotalZeroWhenAbsent Boundary.dominatedConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.dominatedConvergence
    (Boundary.boundary-atom value Boundary.fixedCutoffFiniteSupport ∷ rest)
    (noReasonCons dominated-vs-fixed tail) =
  reasonTotalZeroWhenAbsent Boundary.dominatedConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.dominatedConvergence
    (Boundary.boundary-atom value Boundary.geometricTail ∷ rest)
    (noReasonCons dominated-vs-geometric tail) =
  reasonTotalZeroWhenAbsent Boundary.dominatedConvergence rest tail
reasonTotalZeroWhenAbsent
    Boundary.dominatedConvergence
    (Boundary.boundary-atom value Boundary.strongConvergence ∷ rest)
    (noReasonCons dominated-vs-strong tail) =
  reasonTotalZeroWhenAbsent Boundary.dominatedConvergence rest tail

exactAbsenceCanBeCombinatorial : Bool
exactAbsenceCanBeCombinatorial = true

fixedSupportCanBeEventuallyCombinatorial : Bool
fixedSupportCanBeEventuallyCombinatorial = true

exactAbsenceCanBeCombinatorialIsTrue :
  exactAbsenceCanBeCombinatorial ≡ true
exactAbsenceCanBeCombinatorialIsTrue = refl

fixedSupportCanBeEventuallyCombinatorialIsTrue :
  fixedSupportCanBeEventuallyCombinatorial ≡ true
fixedSupportCanBeEventuallyCombinatorialIsTrue = refl
