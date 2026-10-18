module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection

boundary = Selection.canonicalAdKSourceAtomSelectionBoundary

_ : Selection.thetaOneSelectionsTyped boundary ≡ true
_ = refl

_ : Selection.thetaTwoSelectionsTyped boundary ≡ true
_ = refl

_ : Selection.dLnDomainSelectionsTyped boundary ≡ true
_ = refl

_ : Selection.figureOneSourceLocatorRetained boundary ≡ true
_ = refl

_ : Selection.sameResidueNumberAloneSelectsAtom boundary ≡ false
_ = refl

_ : Selection.sourceLabelCreatesSelectionTruth boundary ≡ false
_ = refl
