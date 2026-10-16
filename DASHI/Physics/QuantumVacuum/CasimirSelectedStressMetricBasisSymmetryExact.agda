module DASHI.Physics.QuantumVacuum.CasimirSelectedStressMetricBasisSymmetryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as SymmetricBasis
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Symmetry
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- SELECTED QFT STRESS -> CANONICAL SYMMETRIC METRIC BASIS
--
-- The generic Brown-Maclay attachment used to request a free component-symmetry
-- theorem for an arbitrary stress evaluator.  The canonical CMP119 route is
-- stronger: one symmetric ten-slot metric basis compiles the ordered-pair
-- evaluator, and its symmetry is theorem output.
--
-- The remaining physical input is therefore not symmetry itself.  It is the
-- same-object representation of the selected restricted QFT stress through
-- this canonical metric-basis readout.
------------------------------------------------------------------------

record SelectedStressMetricBasisRealization
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    Scale Volume : Set
    activity : Chain.SubstitutedActivitySecondVariation
    domain : Domain.CanonicalMetricSourceDomain Scale Volume activity
    representation : StressRep.CanonicalMetricStressRepresentation domain

    symmetricBasis : SymmetricBasis.SymmetricMetricBasisRealization domain
    rationalReadout : Basis.RationalStressPairingReadout representation

    selectedStressToRepresentation :
      QFT.StressTensor (Weld.qftCarriers U) →
      StressRep.StressTensor representation

    SameSelectedStressMetricReadout : Set
    sameSelectedStressMetricReadout : SameSelectedStressMetricReadout

    reading : String

open SelectedStressMetricBasisRealization public

selectedStressMetricBasisEvaluator :
  ∀ {U : Weld.UnifiedCandidate} →
  SelectedStressMetricBasisRealization U →
  Cut.CMP119RationalStressComponentEvaluator
    (QFT.StressTensor (Weld.qftCarriers U))
selectedStressMetricBasisEvaluator realization = record
  { Cut.CMP119RationalStressComponentEvaluator.component =
      λ stress a b →
        Basis.cmp119MetricBasisComponent
          (SymmetricBasis.compileSymmetricBasis16
            (symmetricBasis realization))
          (rationalReadout realization)
          (selectedStressToRepresentation realization stress)
          a b
  }

selectedStressMetricBasisIsSymmetric :
  ∀ {U : Weld.UnifiedCandidate}
    (realization : SelectedStressMetricBasisRealization U)
    (stress : QFT.StressTensor (Weld.qftCarriers U)) →
  Symmetry.PairingComponentSymmetry
    (selectedStressMetricBasisEvaluator realization)
    stress
selectedStressMetricBasisIsSymmetric realization stress =
  Symmetry.metricBasisEvaluatorIsComponentSymmetric
    (symmetricBasis realization)
    (rationalReadout realization)
    (selectedStressToRepresentation realization stress)

------------------------------------------------------------------------
-- Fail-closed authority boundary.
------------------------------------------------------------------------

data AbstractStressSymmetryAutomaticallyIdentifiesMetricBasisReadout : Set where

abstractSymmetryDoesNotIdentifyMetricBasisReadout :
  AbstractStressSymmetryAutomaticallyIdentifiesMetricBasisReadout → ⊥
abstractSymmetryDoesNotIdentifyMetricBasisReadout ()

record CasimirSelectedStressMetricBasisBoundary : Set where
  constructor casimir-selected-stress-metric-basis-boundary
  field
    selectedStressMetricBasisSymmetryCompilerOwned : Bool
    independentRestrictedStressSymmetryPaymentRequired : Bool
    selectedStressMetricBasisSameObjectAttachmentRequired : Bool

open CasimirSelectedStressMetricBasisBoundary public

canonicalSelectedStressMetricBasisBoundary : CasimirSelectedStressMetricBasisBoundary
canonicalSelectedStressMetricBasisBoundary =
  casimir-selected-stress-metric-basis-boundary true false true

casimirSelectedStressMetricBasisReading : String
casimirSelectedStressMetricBasisReading =
  "Coordinate symmetry is compiler output once the selected restricted QFT stress is represented through the repository's canonical symmetric metric basis and rational stress-pairing readout. The remaining physics payment is the same-object attachment of that selected stress/readout to this metric-basis realization, not an independent T_mn=T_nm theorem. Brown-Maclay component values remain separate."
