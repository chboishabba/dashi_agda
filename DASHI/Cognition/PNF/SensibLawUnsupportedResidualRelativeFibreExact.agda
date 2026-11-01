module DASHI.Cognition.PNF.SensibLawUnsupportedResidualRelativeFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineRelativeFibreExact as Fine
import DASHI.Cognition.PNF.SensibLawGWBv01ResidualFrontierCertificationV03Exact as V03

------------------------------------------------------------------------
-- v0.3 tells us that unsupported_dependency is the dominant coarse residual
-- bucket (533,994 / 706,246 residuals).  The next diagnostic refinement keeps
-- that stable coarse code while retaining the actual spaCy dependency label as
-- a relative-fine coordinate.
--
-- This is the merged coarse/fine-fibre theorem shape also independently exposed
-- by the contextual FRACTRAN design work: a valid coarse consumer projection
-- may retain a nontrivial preimage fibre.  No FRACTRAN-specific type is imported
-- here; the runtime stays on the existing direct-delta architecture.
------------------------------------------------------------------------

data UnsupportedCoarse : Set where
  unsupportedDependency : UnsupportedCoarse

DependencyLabel : Set
DependencyLabel = String

coarseUnsupported : DependencyLabel → UnsupportedCoarse
coarseUnsupported _ = unsupportedDependency

relativeDependencyLabel : DependencyLabel → DependencyLabel
relativeDependencyLabel label = label

reopenUnsupported : UnsupportedCoarse → DependencyLabel → DependencyLabel
reopenUnsupported unsupportedDependency label = label

unsupportedRelativeFibre : Fine.CoarseFineReopening DependencyLabel
unsupportedRelativeFibre =
  Fine.coarseFineReopening
    UnsupportedCoarse
    DependencyLabel
    coarseUnsupported
    relativeDependencyLabel
    reopenUnsupported
    (λ label → refl)

coarsePlusDependencyLabelReopensDiagnosticState :
  (label : DependencyLabel) →
  Fine.reopen unsupportedRelativeFibre
    (Fine.coarse unsupportedRelativeFibre label)
    (Fine.relativeFine unsupportedRelativeFibre label)
  ≡ label
coarsePlusDependencyLabelReopensDiagnosticState label =
  Fine.reopenExact unsupportedRelativeFibre label

record ResidualRefinementPlan : Set where
  constructor residualRefinementPlan
  field
    coarseResidualCount : Nat
    totalResidualCount : Nat
    relativeFineCoordinate : String
    preservesEightWayCoarseHistogram : Bool
    changesCanonicalSemanticObservation : Bool
    changesSemanticAuthority : Bool
    requiresSameFineFibreAcrossParityAndDirectPasses : Bool

open ResidualRefinementPlan public

unsupportedDependencyRefinementV04 : ResidualRefinementPlan
unsupportedDependencyRefinementV04 =
  residualRefinementPlan
    (V03.unsupportedDependency V03.canonicalResidualHistogramV03)
    (V03.total V03.canonicalResidualHistogramV03)
    "spacy_dependency_label"
    true
    false
    false
    true

coarseCountPinnedToV03 :
  coarseResidualCount unsupportedDependencyRefinementV04 ≡ 533994
coarseCountPinnedToV03 = refl

data DependencyLabelDeterminesLegalMeaning : Set where
data DiagnosticRefinementCreatesAdmissionAuthority : Set where
data FineResidualRequiresChangingCanonicalConsumerObservation : Set where

dependencyLabelDoesNotDetermineLegalMeaning :
  DependencyLabelDeterminesLegalMeaning → ⊥
dependencyLabelDoesNotDetermineLegalMeaning ()

diagnosticRefinementDoesNotCreateAdmissionAuthority :
  DiagnosticRefinementCreatesAdmissionAuthority → ⊥
diagnosticRefinementDoesNotCreateAdmissionAuthority ()

fineResidualNeedNotChangeCanonicalConsumerObservation :
  FineResidualRequiresChangingCanonicalConsumerObservation → ⊥
fineResidualNeedNotChangeCanonicalConsumerObservation ()
