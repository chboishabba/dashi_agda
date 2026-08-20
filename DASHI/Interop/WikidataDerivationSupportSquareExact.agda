module DASHI.Interop.WikidataDerivationSupportSquareExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Ontology.EpistemicTrit as Trit

infixl 5 _∨ᵇ_

_∨ᵇ_ : Bool → Bool → Bool
true  ∨ᵇ _ = true
false ∨ᵇ x = x

mergeSquare : Four.PolarAssessment → Four.PolarAssessment → Four.PolarAssessment
mergeSquare (Four.assess p n) (Four.assess p′ n′) =
  Four.assess (p ∨ᵇ p′) (n ∨ᵇ n′)

squareFromPolarity : Fibre.DerivationPolarity → Four.PolarAssessment
squareFromPolarity Fibre.supporting = Four.assess true false
squareFromPolarity Fibre.contradicting = Four.assess false true
squareFromPolarity Fibre.unresolved = Four.assess false false

squareOutcome : Four.PolarAssessment → Fibre.FibreOutcome
squareOutcome (Four.assess true false) = Fibre.satisfied
squareOutcome (Four.assess false true) = Fibre.violated
squareOutcome (Four.assess true true) = Fibre.both
squareOutcome (Four.assess false false) = Fibre.undetermined

collapseSquare : Four.PolarAssessment → Trit.EpistemicTrit
collapseSquare (Four.assess true false) = Trit.supported
collapseSquare (Four.assess false true) = Trit.contradicted
collapseSquare (Four.assess true true) = Trit.unresolved
collapseSquare (Four.assess false false) = Trit.unresolved

supportSquare : Four.PolarAssessment
supportSquare = squareFromPolarity Fibre.supporting

contradictionSquare : Four.PolarAssessment
contradictionSquare = squareFromPolarity Fibre.contradicting

ignoranceSquare : Four.PolarAssessment
ignoranceSquare = squareFromPolarity Fibre.unresolved

conflictSquare : Four.PolarAssessment
conflictSquare = mergeSquare supportSquare contradictionSquare

conflictSquareIsBothSupported : conflictSquare ≡ Four.assess true true
conflictSquareIsBothSupported = refl

conflictPositionIsBoth : Four.polarPosition conflictSquare ≡ Tetralemma.both
conflictPositionIsBoth = refl

ignorancePositionIsNeither : Four.polarPosition ignoranceSquare ≡ Tetralemma.neither
ignorancePositionIsNeither = refl

conflictOutcomeIsBoth : squareOutcome conflictSquare ≡ Fibre.both
conflictOutcomeIsBoth = refl

ignoranceOutcomeIsUndetermined : squareOutcome ignoranceSquare ≡ Fibre.undetermined
ignoranceOutcomeIsUndetermined = refl

conflictAndIgnoranceBothCollapseToUnresolved :
  collapseSquare conflictSquare ≡ collapseSquare ignoranceSquare
conflictAndIgnoranceBothCollapseToUnresolved = refl

conflictIsNotIgnorance : conflictSquare ≡ ignoranceSquare → ⊥
conflictIsNotIgnorance ()

oppositeCertifiedSourcesPoolToConflict :
  squareOutcome (mergeSquare
    (squareFromPolarity Fibre.supporting)
    (squareFromPolarity Fibre.contradicting)) ≡ Fibre.both
oppositeCertifiedSourcesPoolToConflict = refl

collapsedConflictIsUnresolved : collapseSquare conflictSquare ≡ Trit.unresolved
collapsedConflictIsUnresolved = refl

collapsedIgnoranceIsUnresolved : collapseSquare ignoranceSquare ≡ Trit.unresolved
collapsedIgnoranceIsUnresolved = refl

tritCannotRecoverConflictFromIgnorance :
  collapseSquare conflictSquare ≡ collapseSquare ignoranceSquare
tritCannotRecoverConflictFromIgnorance = refl
