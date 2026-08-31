module DASHI.Governance.SexedHistoricalTransitionHyperfabricExact where

------------------------------------------------------------------------
-- TRANSITION-BEARING SEXED HISTORICAL HYPERFABRIC
--
-- Cross-pollinates the co-constitution hyperfabric with the repository's
-- transition-residual discipline.  A historical transition is coordinate-wise:
-- formal/legal change, material power, symbolic grammar, religious authority,
-- family relation, epistemic authority and option structure need not move in
-- lockstep.
--
-- The finite epochs and transition statuses below are DASHI comparison
-- specimens.  They are not population laws and do not assert that every person
-- or institution changed in the same way at a named historical moment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact as Hyper
import DASHI.Governance.TransitionResidual as Transition
import DASHI.Governance.InstitutionPreservingRechartAntiSublationExact as Rechart

------------------------------------------------------------------------
-- Historical edges over the existing hyperfabric epochs.
------------------------------------------------------------------------

data HistoricalEdge :
  Hyper.HistoricalEpoch → Hyper.HistoricalEpoch → Set where
  witchOrderToSuffrage :
    HistoricalEdge Hyper.witchTrialOrder Hyper.suffrageRearticulation
  suffrageToReclamation :
    HistoricalEdge Hyper.suffrageRearticulation Hyper.feministWitchReclamation
  reclamationToReciprocal :
    HistoricalEdge Hyper.feministWitchReclamation Hyper.reciprocalReconstitution

------------------------------------------------------------------------
-- Transition coordinates are deliberately not a scalar progress score.
------------------------------------------------------------------------

data TransitionAxis : Set where
  formalPoliticalRepresentation
  legalCapacity
  economicCapacity
  religiousAuthority
  familyAuthority
  sexualNormGrammar
  epistemicAuthority
  symbolicSubjectGrammar
  materialIndependence
  historicalMemory
  : TransitionAxis

data AxisTransitionStatus : Set where
  corrected changed persisted mixed unresolved : AxisTransitionStatus

transitionStatus :
  ∀ {before after} →
  HistoricalEdge before after →
  TransitionAxis →
  AxisTransitionStatus

transitionStatus witchOrderToSuffrage formalPoliticalRepresentation = corrected
transitionStatus witchOrderToSuffrage legalCapacity = changed
transitionStatus witchOrderToSuffrage economicCapacity = mixed
transitionStatus witchOrderToSuffrage religiousAuthority = mixed
transitionStatus witchOrderToSuffrage familyAuthority = mixed
transitionStatus witchOrderToSuffrage sexualNormGrammar = mixed
transitionStatus witchOrderToSuffrage epistemicAuthority = mixed
transitionStatus witchOrderToSuffrage symbolicSubjectGrammar = changed
transitionStatus witchOrderToSuffrage materialIndependence = mixed
transitionStatus witchOrderToSuffrage historicalMemory = persisted

transitionStatus suffrageToReclamation formalPoliticalRepresentation = persisted
transitionStatus suffrageToReclamation legalCapacity = mixed
transitionStatus suffrageToReclamation economicCapacity = mixed
transitionStatus suffrageToReclamation religiousAuthority = changed
transitionStatus suffrageToReclamation familyAuthority = mixed
transitionStatus suffrageToReclamation sexualNormGrammar = changed
transitionStatus suffrageToReclamation epistemicAuthority = changed
transitionStatus suffrageToReclamation symbolicSubjectGrammar = changed
transitionStatus suffrageToReclamation materialIndependence = mixed
transitionStatus suffrageToReclamation historicalMemory = changed

transitionStatus reclamationToReciprocal formalPoliticalRepresentation = mixed
transitionStatus reclamationToReciprocal legalCapacity = mixed
transitionStatus reclamationToReciprocal economicCapacity = mixed
transitionStatus reclamationToReciprocal religiousAuthority = mixed
transitionStatus reclamationToReciprocal familyAuthority = mixed
transitionStatus reclamationToReciprocal sexualNormGrammar = mixed
transitionStatus reclamationToReciprocal epistemicAuthority = mixed
transitionStatus reclamationToReciprocal symbolicSubjectGrammar = changed
transitionStatus reclamationToReciprocal materialIndependence = mixed
transitionStatus reclamationToReciprocal historicalMemory = persisted

------------------------------------------------------------------------
-- Residual-bearing transition receipt.
------------------------------------------------------------------------

record HistoricalTransitionReceipt
    {before after : Hyper.HistoricalEpoch}
    (edge : HistoricalEdge before after) : Set₁ where
  constructor historical-transition-receipt
  field
    status : TransitionAxis → AxisTransitionStatus
    statusMatches : (axis : TransitionAxis) → status axis ≡ transitionStatus edge axis
    unresolvedResidualsRetained : Bool
    unresolvedResidualsRetainedIsTrue : unresolvedResidualsRetained ≡ true
    formalStepPromotesWholeHistoricalClosure : Bool
    formalStepPromotesWholeHistoricalClosureIsFalse :
      formalStepPromotesWholeHistoricalClosure ≡ false

open HistoricalTransitionReceipt public

mkHistoricalTransitionReceipt :
  ∀ {before after}
    (edge : HistoricalEdge before after) →
  HistoricalTransitionReceipt edge
mkHistoricalTransitionReceipt edge =
  historical-transition-receipt
    (transitionStatus edge)
    (λ _ → refl)
    true refl
    false refl

canonicalSuffrageTransitionReceipt :
  HistoricalTransitionReceipt witchOrderToSuffrage
canonicalSuffrageTransitionReceipt =
  mkHistoricalTransitionReceipt witchOrderToSuffrage

canonicalReclamationTransitionReceipt :
  HistoricalTransitionReceipt suffrageToReclamation
canonicalReclamationTransitionReceipt =
  mkHistoricalTransitionReceipt suffrageToReclamation

------------------------------------------------------------------------
-- Formal correction does not recover symbolic/material closure.
-- Two fine transition states can expose the same corrected public/legal surface
-- while retaining different symbolic residuals.
------------------------------------------------------------------------

data FormalCorrectionSurface : Set where
  formalRepresentationCorrected : FormalCorrectionSurface

data SymbolicClosureState : Set where
  symbolicResidualOpen symbolicResidualClosed : SymbolicClosureState

data FineTransitionState : Set where
  correctedWithSymbolicResidual
  correctedWithSymbolicClosure
  : FineTransitionState

formalCorrectionObserver : FineTransitionState → FormalCorrectionSurface
formalCorrectionObserver _ = formalRepresentationCorrected

symbolicClosure : FineTransitionState → SymbolicClosureState
symbolicClosure correctedWithSymbolicResidual = symbolicResidualOpen
symbolicClosure correctedWithSymbolicClosure = symbolicResidualClosed

formalCorrectionCannotRecoverSymbolicClosure :
  INF.FactorsThrough formalCorrectionObserver symbolicClosure → ⊥
formalCorrectionCannotRecoverSymbolicClosure =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      correctedWithSymbolicResidual
      correctedWithSymbolicClosure
      refl
      (λ ()))

------------------------------------------------------------------------
-- Likewise, symbolic reconstitution does not determine material parity.
------------------------------------------------------------------------

data SymbolicReconstitutionSurface : Set where
  positiveRechartPresent : SymbolicReconstitutionSurface

data MaterialParityState : Set where
  materialAsymmetryRetained materialParityReached : MaterialParityState

data RechartFineState : Set where
  rechartWithAsymmetry rechartWithParity : RechartFineState

symbolicRechartObserver : RechartFineState → SymbolicReconstitutionSurface
symbolicRechartObserver _ = positiveRechartPresent

materialParity : RechartFineState → MaterialParityState
materialParity rechartWithAsymmetry = materialAsymmetryRetained
materialParity rechartWithParity = materialParityReached

symbolicRechartCannotRecoverMaterialParity :
  INF.FactorsThrough symbolicRechartObserver materialParity → ⊥
symbolicRechartCannotRecoverMaterialParity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      rechartWithAsymmetry
      rechartWithParity
      refl
      (λ ()))

------------------------------------------------------------------------
-- Cross-pollination with existing transition and anti-sublation owners.
------------------------------------------------------------------------

transitionResidualRuleRetainsUnresolvedAxes : Bool
transitionResidualRuleRetainsUnresolvedAxes =
  Transition.TransitionAuthorityBoundary.unresolvedResidualsMayBeErased
    Transition.canonicalTransitionAuthorityBoundary

transitionResidualRuleRetainsUnresolvedAxesIsFalse :
  transitionResidualRuleRetainsUnresolvedAxes ≡ false
transitionResidualRuleRetainsUnresolvedAxesIsFalse = refl

quietOrderStillDoesNotDetermineJustice =
  Rechart.quietSurfaceDoesNotDetermineJustice

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data SuffrageCorrectionImpliesWholePowerParity : Set where

data SymbolicReconstitutionImpliesMaterialRepair : Set where

data MaterialIndependenceImpliesSymbolicDeconstruction : Set where

data OneChangedAxisClosesTransition : Set where

suffrageCorrectionDoesNotImplyWholePowerParity :
  SuffrageCorrectionImpliesWholePowerParity → ⊥
suffrageCorrectionDoesNotImplyWholePowerParity ()

symbolicReconstitutionDoesNotImplyMaterialRepair :
  SymbolicReconstitutionImpliesMaterialRepair → ⊥
symbolicReconstitutionDoesNotImplyMaterialRepair ()

materialIndependenceDoesNotImplySymbolicDeconstruction :
  MaterialIndependenceImpliesSymbolicDeconstruction → ⊥
materialIndependenceDoesNotImplySymbolicDeconstruction ()

oneChangedAxisDoesNotCloseTransition :
  OneChangedAxisClosesTransition → ⊥
oneChangedAxisDoesNotCloseTransition ()

record SexedHistoricalTransitionBoundary : Set where
  constructor sexed-historical-transition-boundary
  field
    formalPoliticalCorrectionMeansWholePowerParity : Bool
    symbolicReconstitutionMeansMaterialRepair : Bool
    materialIndependenceMeansInheritedGrammarGone : Bool
    oneAxisChangeMeansHistoricalClosure : Bool
    unresolvedResidualsMustRemainRepresentable : Bool
    transitionIsCoordinateWise : Bool

canonicalSexedHistoricalTransitionBoundary :
  SexedHistoricalTransitionBoundary
canonicalSexedHistoricalTransitionBoundary =
  sexed-historical-transition-boundary
    false false false false true true
