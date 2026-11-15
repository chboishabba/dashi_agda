module DASHI.Philosophy.NonginGenealogyOwnerWeldValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginGenealogyOwnerWeldExact as Weld

boundary : Weld.NonginGenealogyOwnerWeldBoundary
boundary = Weld.canonicalNonginGenealogyOwnerWeldBoundary

allTypedDescendantOwnersLinked :
  Weld.allTypedDescendantOwnersLinked boundary ≡ true
allTypedDescendantOwnersLinked = refl

metaPositionTypedOwnerLinked :
  Weld.metaPositionTypedOwnerLinked boundary ≡ true
metaPositionTypedOwnerLinked = refl

hierarchicalRefinementTypedOwnerLinked :
  Weld.hierarchicalRefinementTypedOwnerLinked boundary ≡ true
hierarchicalRefinementTypedOwnerLinked = refl

thresholdResidualTypedOwnerLinked :
  Weld.thresholdResidualTypedOwnerLinked boundary ≡ true
thresholdResidualTypedOwnerLinked = refl

relationalProcessTypedOwnerLinked :
  Weld.relationalProcessTypedOwnerLinked boundary ≡ true
relationalProcessTypedOwnerLinked = refl

operationalStageMotifBoundaryLinked :
  Weld.operationalStageMotifBoundaryLinked boundary ≡ true
operationalStageMotifBoundaryLinked = refl

sourceGenealogyNotIdentifiedWithLaterMathematics :
  Weld.sourceGenealogyIdentifiedWithLaterMathematics boundary ≡ false
sourceGenealogyNotIdentifiedWithLaterMathematics = refl
