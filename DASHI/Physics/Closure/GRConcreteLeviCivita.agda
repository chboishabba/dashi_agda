module DASHI.Physics.Closure.GRConcreteLeviCivita where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G3SelectedCarrierInstance as G3Sel
import DASHI.Physics.Closure.ContinuumLimitTheorem as Continuum
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GR
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild

------------------------------------------------------------------------
-- Concrete flat Levi-Civita surface over the selected FactorVec state.
--
-- The selected G3 state fixes a local DASHIState whose Carrier is exactly
-- FactorVec.  The GR sidecar already contains a definitional flat
-- Minkowski finite-r Levi-Civita closure.  This module ties those two facts
-- together without claiming non-flat GR, Ricci contraction, Bianchi, or
-- Einstein promotion.

data GRConcreteLeviCivitaStatus : Set where
  selectedFlatMinkowskiLeviCivitaPrerequisiteClosed :
    GRConcreteLeviCivitaStatus

data GRConcreteLeviCivitaResidual : Set where
  nonFlatSelectedGRStillOpen :
    GRConcreteLeviCivitaResidual

  selectedFourChartLeviCivitaAdapterStaged :
    GRConcreteLeviCivitaResidual

canonicalGRConcreteFlatLeviCivitaClosure :
  GR.GRFlatMinkowskiFiniteRLeviCivitaClosure
canonicalGRConcreteFlatLeviCivitaClosure =
  GR.canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure

record GRConcreteLeviCivitaSurface : Setω where
  field
    status :
      GRConcreteLeviCivitaStatus

    selectedCarrierIsFactorVec :
      G3Sel.selectedCarrierIsFactorVec
      ≡
      refl

    selectedCarrierValueLaw :
      G3Sel.selectedCarrierValueFactorVec
      ≡
      refl

    selectedP2BumpLaw :
      G3Sel.selectedP2BumpExponentLaw
      ≡
      G3Sel.selectedP2BumpExponentLaw

    flatMetricAtIsMinkowski :
      (base : ML.MinkowskiCarrier) →
      GR.flatConstantMetricAt base
      ≡
      ML.minkowskiQuadratic

    flatConnectionAtIsTrivial :
      (base : ML.MinkowskiCarrier) →
      GR.flatConstantConnectionAt base
      ≡
      tt

    flatMetricCompatibility :
      (base : ML.MinkowskiCarrier) →
      GR.GRMetricCompatibleLeviCivitaCarrierObligation.metricCompatibility
        GR.canonicalGRFlatConstantMetricCompatibleCarrier
        (GR.flatConstantMetricAt base)
        (GR.flatConstantConnectionAt base)

    flatConnectionIsLeviCivita :
      (base : ML.MinkowskiCarrier) →
      GR.GRMetricCompatibleLeviCivitaCarrierObligation.carrierConnectionIsLeviCivita
        GR.canonicalGRFlatConstantMetricCompatibleCarrier
        base

    flatChristoffelTorsionFree :
      (base : ML.MinkowskiCarrier) →
      (lambda mu nu : GR.FlatCoordinateIndex) →
      GR.GRStandardLeviCivitaAlgebraLawObligation.christoffelSymbol
        GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        (GR.GRStandardLeviCivitaAlgebraLawObligation.connectionAt
          GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
          base)
        lambda
        mu
        nu
      ≡
      GR.GRStandardLeviCivitaAlgebraLawObligation.christoffelSymbol
        GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        (GR.GRStandardLeviCivitaAlgebraLawObligation.connectionAt
          GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
          base)
        lambda
        nu
        mu

    flatSixTermCancellation :
      (base : ML.MinkowskiCarrier) →
      (lambda mu nu : GR.FlatCoordinateIndex) →
      GR.GRStandardLeviCivitaAlgebraLawObligation.sixTermRicciIdentityCancellation
        GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        base
        lambda
        mu
        nu

    flatTraceEqualsFour :
      (metric : GR.FlatMetricCarrier) →
      GR.GRStandardLeviCivitaAlgebraLawObligation.traceEqualsFourLaw
        GR.canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        metric

    residual :
      GRConcreteLeviCivitaResidual

    residualIsNonFlatSelectedGROpen :
      residual
      ≡
      nonFlatSelectedGRStillOpen

    remainingSelectedGRFirstMissing :
      GR.GRDiscreteBianchiFiniteRMissingIngredient

    remainingSelectedGRFirstMissingIsFiniteRScalarAlgebra :
      remainingSelectedGRFirstMissing
      ≡
      GR.missingFiniteRScalarAlgebra

    nonPromotionBoundary :
      List String

canonicalGRConcreteLeviCivitaSurface :
  GRConcreteLeviCivitaSurface
canonicalGRConcreteLeviCivitaSurface =
  record
    { status =
        selectedFlatMinkowskiLeviCivitaPrerequisiteClosed
    ; selectedCarrierIsFactorVec =
        refl
    ; selectedCarrierValueLaw =
        refl
    ; selectedP2BumpLaw =
        refl
    ; flatMetricAtIsMinkowski =
        λ _ → refl
    ; flatConnectionAtIsTrivial =
        λ _ → refl
    ; flatMetricCompatibility =
        λ _ → tt
    ; flatConnectionIsLeviCivita =
        λ _ → tt
    ; flatChristoffelTorsionFree =
        λ _ _ _ _ → refl
    ; flatSixTermCancellation =
        λ _ _ _ _ → tt
    ; flatTraceEqualsFour =
        λ _ → tt
    ; residual =
        nonFlatSelectedGRStillOpen
    ; residualIsNonFlatSelectedGROpen =
        refl
    ; remainingSelectedGRFirstMissing =
        GR.missingFiniteRScalarAlgebra
    ; remainingSelectedGRFirstMissingIsFiniteRScalarAlgebra =
        refl
    ; nonPromotionBoundary =
        "Selected FactorVec DASHIState is available through G3SelectedCarrierInstance"
        ∷ "Flat constant Minkowski Levi-Civita closure is reused from GRDiscreteBianchiFiniteR"
        ∷ "Metric compatibility, torsion-free Christoffel symmetry, six-term cancellation, and trace law are inhabited only on the flat constant prerequisite"
        ∷ "This module does not construct the selected non-flat finite-r Levi-Civita connection"
        ∷ "This module does not promote GR, contracted Bianchi, Ricci-zero, Einstein tensor, G6, or W7"
        ∷ []
    }

grConcreteLeviCivitaResidualIsNonFlat :
  GRConcreteLeviCivitaSurface.residual
    canonicalGRConcreteLeviCivitaSurface
  ≡
  nonFlatSelectedGRStillOpen
grConcreteLeviCivitaResidualIsNonFlat =
  refl

grConcreteLeviCivitaFirstMissingIsFiniteRScalarAlgebra :
  GRConcreteLeviCivitaSurface.remainingSelectedGRFirstMissing
    canonicalGRConcreteLeviCivitaSurface
  ≡
  GR.missingFiniteRScalarAlgebra
grConcreteLeviCivitaFirstMissingIsFiniteRScalarAlgebra =
  refl

------------------------------------------------------------------------
-- Selected finite-r Levi-Civita adapter.
--
-- This is the non-flat lane's strongest local checked surface available in
-- the current repository.  It consumes the selected four-chart metric table
-- from GRNonFlatScalarAlgebraSurface: identity metric, zero metric
-- derivatives, and zero Christoffel symbols over coord0..coord3.  The
-- Christoffel formula, torsion symmetry, and metric compatibility are
-- inhabited on that finite selected table.  It is deliberately not promoted
-- to a Schwarzschild continuum theorem or terminal GR/W4 result.

data GRConcreteSelectedLeviCivitaAdapterStatus : Set where
  selectedFourChartChristoffelLeviCivitaWitnessNoPromotion :
    GRConcreteSelectedLeviCivitaAdapterStatus

record GRConcreteSelectedLeviCivitaAdapter : Setω where
  field
    status :
      GRConcreteSelectedLeviCivitaAdapterStatus

    metricCompatibilityReceipt :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt

    selectedGeometryStaging :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    discreteBianchiProgress :
      GR.GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt

    selectedTorsionFreeChristoffel :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRChristoffelSymbol
        (NFScalar.grSelectedFiniteRConnectionAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.grSelectedFiniteRChristoffelSymbol
        (NFScalar.grSelectedFiniteRConnectionAt base)
        lambda
        nu
        mu

    selectedMetricCompatibility :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRCovariantDerivativeOfMetric
        (NFScalar.grSelectedFiniteRConnectionAt base)
        (NFScalar.grSelectedFiniteRMetricAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.r0

    selectedChristoffelForm :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (NFScalar.grSelectedFiniteRChristoffelSymbol
          (NFScalar.grSelectedFiniteRConnectionAt base)
          lambda
          mu
          nu)
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              (NFScalar.grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                (NFScalar.grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    missingCarrierConnectionIsLeviCivitaMarker :
      GR.GRDiscreteBianchiFiniteRMissingIngredient

    missingCarrierConnectionIsLeviCivitaMarkerIsCanonical :
      missingCarrierConnectionIsLeviCivitaMarker
      ≡
      GR.missingCarrierConnectionIsLeviCivita

    missingCarrierConnectionIsLeviCivitaDischargedLocally :
      Bool

    missingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue :
      missingCarrierConnectionIsLeviCivitaDischargedLocally
      ≡
      true

    nextResidualAfterSelectedLeviCivita :
      GR.GRDiscreteBianchiFiniteRMissingIngredient

    nextResidualAfterSelectedLeviCivitaIsCurvatureRicciEinsteinBoundary :
      nextResidualAfterSelectedLeviCivita
      ≡
      GR.missingCurvatureToRicciEinsteinContractionBoundary

    unsupportedSchwarzschildContinuumPromotion :
      Bool

    unsupportedSchwarzschildContinuumPromotionIsFalse :
      unsupportedSchwarzschildContinuumPromotion
      ≡
      false

    unsupportedTerminalPromotion :
      Bool

    unsupportedTerminalPromotionIsFalse :
      unsupportedTerminalPromotion
      ≡
      false

    adapterBoundary :
      List String

schwarzschildChristoffelIsLeviCivita :
  (base : NFScalar.GRFiniteRChartPoint) →
  (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grFiniteRScalarMul
    NFScalar.r2
    (NFScalar.grSelectedFiniteRChristoffelSymbol
      (NFScalar.grSelectedFiniteRConnectionAt base)
      lambda
      mu
      nu)
  ≡
  NFScalar.grSelectedFiniteRContract
    (λ rho →
      NFScalar.grFiniteRScalarMul
        (NFScalar.grSelectedFiniteRInverseMetricComponent
          (NFScalar.grSelectedFiniteRMetricAt base)
          lambda
          rho)
        (NFScalar.grFiniteRScalarSub
          (NFScalar.grFiniteRScalarAdd
            (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
              (NFScalar.grSelectedFiniteRMetricAt base)
              mu
              nu
              rho)
            (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
              (NFScalar.grSelectedFiniteRMetricAt base)
              nu
              mu
              rho))
          (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
            (NFScalar.grSelectedFiniteRMetricAt base)
            rho
            mu
            nu)))
schwarzschildChristoffelIsLeviCivita =
  NFScalar.grSelectedFiniteRLeviCivitaConnectionEquality

canonicalGRConcreteSelectedLeviCivitaAdapter :
  GRConcreteSelectedLeviCivitaAdapter
canonicalGRConcreteSelectedLeviCivitaAdapter =
  record
    { status =
        selectedFourChartChristoffelLeviCivitaWitnessNoPromotion
    ; metricCompatibilityReceipt =
        NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; selectedGeometryStaging =
        NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; discreteBianchiProgress =
        GR.canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; selectedTorsionFreeChristoffel =
        λ _ _ _ _ → refl
    ; selectedMetricCompatibility =
        NFScalar.grFlatSelectedFiniteChartMetricCompatibilityTheorem
    ; selectedChristoffelForm =
        schwarzschildChristoffelIsLeviCivita
    ; missingCarrierConnectionIsLeviCivitaMarker =
        GR.GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.carrierConnectionIsLeviCivitaMarkerDischarged
          GR.canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; missingCarrierConnectionIsLeviCivitaMarkerIsCanonical =
        GR.GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.carrierConnectionIsLeviCivitaMarkerDischargedIsCanonical
          GR.canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; missingCarrierConnectionIsLeviCivitaDischargedLocally =
        true
    ; missingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue =
        refl
    ; nextResidualAfterSelectedLeviCivita =
        GR.GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.postGeometryPromotionResidualBlocker
          GR.canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; nextResidualAfterSelectedLeviCivitaIsCurvatureRicciEinsteinBoundary =
        GR.GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.postGeometryPromotionResidualBlockerIsCurvatureToRicciEinsteinBoundary
          GR.canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; unsupportedSchwarzschildContinuumPromotion =
        false
    ; unsupportedSchwarzschildContinuumPromotionIsFalse =
        refl
    ; unsupportedTerminalPromotion =
        false
    ; unsupportedTerminalPromotionIsFalse =
        refl
    ; adapterBoundary =
        "schwarzschildChristoffelIsLeviCivita names the selected finite four-chart zero-table Christoffel-from-metric witness"
        ∷ "The adapter consumes torsion-free symmetry, metric compatibility, and Christoffel-form evidence for the selected finite table"
        ∷ "The local missingCarrierConnectionIsLeviCivita marker is discharged by GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt"
        ∷ "The next residual is the curvature-to-Ricci/Einstein contraction boundary"
        ∷ "No Schwarzschild continuum limit, non-flat sourced Einstein equation, W4, or terminal GR promotion is asserted"
        ∷ []
    }

grConcreteSelectedLeviCivitaAdapterClosesCarrierConnection :
  GRConcreteSelectedLeviCivitaAdapter.missingCarrierConnectionIsLeviCivitaDischargedLocally
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  true
grConcreteSelectedLeviCivitaAdapterClosesCarrierConnection =
  refl

grConcreteSelectedLeviCivitaAdapterNextResidual :
  GRConcreteSelectedLeviCivitaAdapter.nextResidualAfterSelectedLeviCivita
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  GR.missingCurvatureToRicciEinsteinContractionBoundary
grConcreteSelectedLeviCivitaAdapterNextResidual =
  refl

grConcreteSelectedLeviCivitaAdapterNoSchwarzschildPromotion :
  GRConcreteSelectedLeviCivitaAdapter.unsupportedSchwarzschildContinuumPromotion
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  false
grConcreteSelectedLeviCivitaAdapterNoSchwarzschildPromotion =
  refl

canonicalSelectedLeviCivitaMissingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue :
  GRConcreteSelectedLeviCivitaAdapter.missingCarrierConnectionIsLeviCivitaDischargedLocally
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  true
canonicalSelectedLeviCivitaMissingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue =
  GRConcreteSelectedLeviCivitaAdapter.missingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue
    canonicalGRConcreteSelectedLeviCivitaAdapter

canonicalSelectedLeviCivitaUnsupportedSchwarzschildContinuumPromotionIsFalse :
  GRConcreteSelectedLeviCivitaAdapter.unsupportedSchwarzschildContinuumPromotion
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  false
canonicalSelectedLeviCivitaUnsupportedSchwarzschildContinuumPromotionIsFalse =
  GRConcreteSelectedLeviCivitaAdapter.unsupportedSchwarzschildContinuumPromotionIsFalse
    canonicalGRConcreteSelectedLeviCivitaAdapter

canonicalSelectedLeviCivitaSelectedChristoffelFormIsSchwarzschildChristoffelIsLeviCivita :
  GRConcreteSelectedLeviCivitaAdapter.selectedChristoffelForm
    canonicalGRConcreteSelectedLeviCivitaAdapter
  ≡
  schwarzschildChristoffelIsLeviCivita
canonicalSelectedLeviCivitaSelectedChristoffelFormIsSchwarzschildChristoffelIsLeviCivita =
  refl

grConcreteSelectedLeviCivitaSelectedTorsionFreeChristoffel :
  (base : NFScalar.GRFiniteRChartPoint) →
  (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grSelectedFiniteRChristoffelSymbol
    (NFScalar.grSelectedFiniteRConnectionAt base)
    lambda
    mu
    nu
  ≡
  NFScalar.grSelectedFiniteRChristoffelSymbol
    (NFScalar.grSelectedFiniteRConnectionAt base)
    lambda
    nu
    mu
grConcreteSelectedLeviCivitaSelectedTorsionFreeChristoffel =
  GRConcreteSelectedLeviCivitaAdapter.selectedTorsionFreeChristoffel
    canonicalGRConcreteSelectedLeviCivitaAdapter

grConcreteSelectedLeviCivitaSelectedMetricCompatibility :
  (base : NFScalar.GRFiniteRChartPoint) →
  (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grSelectedFiniteRCovariantDerivativeOfMetric
    (NFScalar.grSelectedFiniteRConnectionAt base)
    (NFScalar.grSelectedFiniteRMetricAt base)
    lambda
    mu
    nu
  ≡
  NFScalar.r0
grConcreteSelectedLeviCivitaSelectedMetricCompatibility =
  GRConcreteSelectedLeviCivitaAdapter.selectedMetricCompatibility
    canonicalGRConcreteSelectedLeviCivitaAdapter

grConcreteSelectedLeviCivitaSelectedChristoffelForm :
  (base : NFScalar.GRFiniteRChartPoint) →
  (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grFiniteRScalarMul
    NFScalar.r2
    (NFScalar.grSelectedFiniteRChristoffelSymbol
      (NFScalar.grSelectedFiniteRConnectionAt base)
      lambda
      mu
      nu)
  ≡
  NFScalar.grSelectedFiniteRContract
    (λ rho →
      NFScalar.grFiniteRScalarMul
        (NFScalar.grSelectedFiniteRInverseMetricComponent
          (NFScalar.grSelectedFiniteRMetricAt base)
          lambda
          rho)
        (NFScalar.grFiniteRScalarSub
          (NFScalar.grFiniteRScalarAdd
            (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
              (NFScalar.grSelectedFiniteRMetricAt base)
              mu
              nu
              rho)
            (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
              (NFScalar.grSelectedFiniteRMetricAt base)
              nu
              mu
              rho))
          (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
            (NFScalar.grSelectedFiniteRMetricAt base)
            rho
            mu
            nu)))
grConcreteSelectedLeviCivitaSelectedChristoffelForm =
  GRConcreteSelectedLeviCivitaAdapter.selectedChristoffelForm
    canonicalGRConcreteSelectedLeviCivitaAdapter

record GRConcreteSelectedLeviCivitaLocalHandoff : Setω where
  field
    torsionFreeChristoffel :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRChristoffelSymbol
        (NFScalar.grSelectedFiniteRConnectionAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.grSelectedFiniteRChristoffelSymbol
        (NFScalar.grSelectedFiniteRConnectionAt base)
        lambda
        nu
        mu

    metricCompatibility :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRCovariantDerivativeOfMetric
        (NFScalar.grSelectedFiniteRConnectionAt base)
        (NFScalar.grSelectedFiniteRMetricAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.r0

    christoffelForm :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (NFScalar.grSelectedFiniteRChristoffelSymbol
          (NFScalar.grSelectedFiniteRConnectionAt base)
          lambda
          mu
          nu)
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              (NFScalar.grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                (NFScalar.grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    localCarrierConnectionDischarged :
      GRConcreteSelectedLeviCivitaAdapter.missingCarrierConnectionIsLeviCivitaDischargedLocally
        canonicalGRConcreteSelectedLeviCivitaAdapter
      ≡
      true

    noSchwarzschildContinuumPromotion :
      GRConcreteSelectedLeviCivitaAdapter.unsupportedSchwarzschildContinuumPromotion
        canonicalGRConcreteSelectedLeviCivitaAdapter
      ≡
      false

    christoffelFormIsNamedProjection :
      christoffelForm
      ≡
      schwarzschildChristoffelIsLeviCivita

canonicalGRConcreteSelectedLeviCivitaLocalHandoff :
  GRConcreteSelectedLeviCivitaLocalHandoff
canonicalGRConcreteSelectedLeviCivitaLocalHandoff =
  record
    { torsionFreeChristoffel =
        grConcreteSelectedLeviCivitaSelectedTorsionFreeChristoffel
    ; metricCompatibility =
        grConcreteSelectedLeviCivitaSelectedMetricCompatibility
    ; christoffelForm =
        grConcreteSelectedLeviCivitaSelectedChristoffelForm
    ; localCarrierConnectionDischarged =
        canonicalSelectedLeviCivitaMissingCarrierConnectionIsLeviCivitaDischargedLocallyIsTrue
    ; noSchwarzschildContinuumPromotion =
        canonicalSelectedLeviCivitaUnsupportedSchwarzschildContinuumPromotionIsFalse
    ; christoffelFormIsNamedProjection =
        canonicalSelectedLeviCivitaSelectedChristoffelFormIsSchwarzschildChristoffelIsLeviCivita
    }

------------------------------------------------------------------------
-- Selected Schwarzschild Levi-Civita / Koszul handoff.
--
-- The Schwarzschild candidate module exposes an inspected r_s = 2, r = 3
-- point table.  This handoff records only the checked finite/table laws that
-- can be consumed locally: torsion-free shape by lower-index Christoffel
-- symmetry, metric-compatibility shape by the Koszul/Tier-1 symmetric
-- metric/inverse-metric table, and the Christoffel-form projection by refl
-- against the selected table.  It deliberately routes the remaining analytic
-- work to Christoffel C0 stability/kernel control and not back to the carrier
-- connection existence marker.

data GRConcreteSelectedSchwarzschildAnalyticBlocker : Set where
  christoffelC0StabilityKernelBlocker :
    GRConcreteSelectedSchwarzschildAnalyticBlocker

record GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff : Setω where
  field
    analyticTable :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt

    selectedFiniteHandoff :
      GRConcreteSelectedLeviCivitaLocalHandoff

    torsionFreeByChristoffelSymmetry :
      (upper lower₁ lower₂ : Schwarzschild.SchwarzschildCoordinateIndex) →
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
        analyticTable
        upper
        lower₁
        lower₂
      ≡
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
        analyticTable
        upper
        lower₂
        lower₁

    metricCompatibilityViaKoszulTier1MetricSymmetry :
      (kind : Schwarzschild.SchwarzschildMetricDerivativeKind)
      (i j : Schwarzschild.SchwarzschildCoordinateIndex) →
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.metricAndRadialDerivative
        analyticTable
        kind
        i
        j
      ≡
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.metricAndRadialDerivative
        analyticTable
        kind
        j
        i

    metricCompatibilityViaKoszulTier1InverseSymmetry :
      (i j : Schwarzschild.SchwarzschildCoordinateIndex) →
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.inverseMetric
        analyticTable
        i
        j
      ≡
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.inverseMetric
        analyticTable
        j
        i

    selectedFiniteMetricCompatibilityLaw :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRCovariantDerivativeOfMetric
        (NFScalar.grSelectedFiniteRConnectionAt base)
        (NFScalar.grSelectedFiniteRMetricAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.r0

    christoffelFormReflAtSelectedTable :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.christoffel analyticTable
      ≡
      Schwarzschild.schwarzschildGammaAtRs2R3

    doubledChristoffelFormReflAtSelectedTable :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel analyticTable
      ≡
      Schwarzschild.schwarzschildTwoGammaAtRs2R3

    selectedFiniteChristoffelForm :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (NFScalar.grSelectedFiniteRChristoffelSymbol
          (NFScalar.grSelectedFiniteRConnectionAt base)
          lambda
          mu
          nu)
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              (NFScalar.grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                (NFScalar.grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    carrierConnectionHandoffClosedLocally :
      GRConcreteSelectedLeviCivitaLocalHandoff.localCarrierConnectionDischarged
        selectedFiniteHandoff
      ≡
      GRConcreteSelectedLeviCivitaLocalHandoff.localCarrierConnectionDischarged
        canonicalGRConcreteSelectedLeviCivitaLocalHandoff

    remainingAnalyticBlocker :
      GRConcreteSelectedSchwarzschildAnalyticBlocker

    remainingAnalyticBlockerIsChristoffelC0StabilityKernel :
      remainingAnalyticBlocker
      ≡
      christoffelC0StabilityKernelBlocker

    routesBlockerToCarrierConnection :
      Bool

    routesBlockerToCarrierConnectionIsFalse :
      routesBlockerToCarrierConnection
      ≡
      false

    routesBlockerToChristoffelC0StabilityKernel :
      Bool

    routesBlockerToChristoffelC0StabilityKernelIsTrue :
      routesBlockerToChristoffelC0StabilityKernel
      ≡
      true

    schwarzschildContinuumPromotion :
      Bool

    schwarzschildContinuumPromotionIsFalse :
      schwarzschildContinuumPromotion
      ≡
      false

    vacuumPromotionIsStillFalse :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotion
        analyticTable
      ≡
      false

    handoffBoundary :
      List String

canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff :
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff
canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff =
  record
    { analyticTable =
        Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; selectedFiniteHandoff =
        canonicalGRConcreteSelectedLeviCivitaLocalHandoff
    ; torsionFreeByChristoffelSymmetry =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffelLowerSymmetry
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; metricCompatibilityViaKoszulTier1MetricSymmetry =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.metricAndRadialDerivativeSymmetric
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; metricCompatibilityViaKoszulTier1InverseSymmetry =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.inverseMetricSymmetric
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; selectedFiniteMetricCompatibilityLaw =
        grConcreteSelectedLeviCivitaSelectedMetricCompatibility
    ; christoffelFormReflAtSelectedTable =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.christoffelIsCanonical
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; doubledChristoffelFormReflAtSelectedTable =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffelIsCanonical
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; selectedFiniteChristoffelForm =
        grConcreteSelectedLeviCivitaSelectedChristoffelForm
    ; carrierConnectionHandoffClosedLocally =
        refl
    ; remainingAnalyticBlocker =
        christoffelC0StabilityKernelBlocker
    ; remainingAnalyticBlockerIsChristoffelC0StabilityKernel =
        refl
    ; routesBlockerToCarrierConnection =
        false
    ; routesBlockerToCarrierConnectionIsFalse =
        refl
    ; routesBlockerToChristoffelC0StabilityKernel =
        true
    ; routesBlockerToChristoffelC0StabilityKernelIsTrue =
        refl
    ; schwarzschildContinuumPromotion =
        false
    ; schwarzschildContinuumPromotionIsFalse =
        refl
    ; vacuumPromotionIsStillFalse =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotionIsFalse
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; handoffBoundary =
        "Torsion-free is exposed only as selected Schwarzschild point-table lower-index Christoffel symmetry"
        ∷ "Metric compatibility is exposed only as Koszul/Tier-1 law shape: symmetric metric and inverse-metric table plus the existing finite selected covariant-derivative zero law"
        ∷ "Christoffel form is a refl projection at the selected Schwarzschild point table and the selected finite four-chart table"
        ∷ "The carrier connection handoff is closed locally by the selected finite Levi-Civita adapter"
        ∷ "The remaining analytic blocker is Christoffel C0 stability/kernel control, not carrier connection existence"
        ∷ "No continuum Schwarzschild, vacuum, Ricci-zero theorem, W4, or terminal GR promotion is introduced"
        ∷ []
    }

grConcreteSelectedSchwarzschildTorsionFreeByChristoffelSymmetry :
  (upper lower₁ lower₂ : Schwarzschild.SchwarzschildCoordinateIndex) →
  Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
    Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    upper
    lower₁
    lower₂
  ≡
  Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
    Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    upper
    lower₂
    lower₁
grConcreteSelectedSchwarzschildTorsionFreeByChristoffelSymmetry =
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff.torsionFreeByChristoffelSymmetry
    canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff

grConcreteSelectedSchwarzschildMetricCompatibilityKoszulMetricSymmetry :
  (kind : Schwarzschild.SchwarzschildMetricDerivativeKind)
  (i j : Schwarzschild.SchwarzschildCoordinateIndex) →
  Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.metricAndRadialDerivative
    Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    kind
    i
    j
  ≡
  Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.metricAndRadialDerivative
    Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    kind
    j
    i
grConcreteSelectedSchwarzschildMetricCompatibilityKoszulMetricSymmetry =
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff.metricCompatibilityViaKoszulTier1MetricSymmetry
    canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff

grConcreteSelectedSchwarzschildChristoffelFormReflAtSelectedTable :
  Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.christoffel
    Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
  ≡
  Schwarzschild.schwarzschildGammaAtRs2R3
grConcreteSelectedSchwarzschildChristoffelFormReflAtSelectedTable =
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff.christoffelFormReflAtSelectedTable
    canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff

grConcreteSelectedSchwarzschildRemainingBlockerIsChristoffelC0StabilityKernel :
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff.remainingAnalyticBlocker
    canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff
  ≡
  christoffelC0StabilityKernelBlocker
grConcreteSelectedSchwarzschildRemainingBlockerIsChristoffelC0StabilityKernel =
  refl

grConcreteSelectedSchwarzschildNoContinuumPromotion :
  GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff.schwarzschildContinuumPromotion
    canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff
  ≡
  false
grConcreteSelectedSchwarzschildNoContinuumPromotion =
  refl

------------------------------------------------------------------------
-- Analytic blocker statement after the selected Levi-Civita/Koszul handoff.
--
-- The selected handoff above is intentionally local: torsion-free and
-- metric-compatibility evidence is available only on selected finite/table
-- surfaces.  The shell constants imported from Schwarzschild name the
-- interval-control budget, and the qualified Continuum import names the
-- symbolic-rational C0 kernel surface.  This receipt makes that routing
-- explicit without constructing a kernel inhabitant or Ricci extraction
-- theorem.

data GRConcreteFullIntervalChristoffelC0StabilityBlocker : Set where
  fullIntervalChristoffelC0StabilityRequired :
    GRConcreteFullIntervalChristoffelC0StabilityBlocker

data GRConcreteSelectedC0RicciExtractionBlocker : Set where
  christoffelC0StabilityKernelAndRicciExtractionBlocker :
    GRConcreteSelectedC0RicciExtractionBlocker

record GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt : Setω where
  field
    selectedKoszulHandoff :
      GRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff

    selectedTorsionIsLocalOnly :
      Bool

    selectedTorsionIsLocalOnlyIsTrue :
      selectedTorsionIsLocalOnly
      ≡
      true

    selectedMetricCompatibilityIsLocalOnly :
      Bool

    selectedMetricCompatibilityIsLocalOnlyIsTrue :
      selectedMetricCompatibilityIsLocalOnly
      ≡
      true

    selectedChristoffelFormIsPointTableOnly :
      Bool

    selectedChristoffelFormIsPointTableOnlyIsTrue :
      selectedChristoffelFormIsPointTableOnly
      ≡
      true

    shellSupremumBounds :
      Schwarzschild.SchwarzschildShellSupremumBoundsReceipt

    shellSupremumBoundsAreCanonical :
      shellSupremumBounds
      ≡
      Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt

    shellParameters :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt

    shellParametersAreCanonical :
      shellParameters
      ≡
      Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt

    shellConstants :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt

    shellConstantsAreCanonical :
      shellConstants
      ≡
      Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt

    shellRsIsTwo :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRs
        shellParameters
      ≡
      Schwarzschild.twoN

    shellRMinIsThree :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMin
        shellParameters
      ≡
      Schwarzschild.threeN

    shellRMaxIsThree :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMax
        shellParameters
      ≡
      Schwarzschild.threeN

    shellDeltaIsOne :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellDelta
        shellParameters
      ≡
      Schwarzschild.oneN

    tightMaxAbsDrGammaIsOne :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.tightMaxAbsDrGamma
        shellConstants
      ≡
      Schwarzschild.posOne

    conservativeShellCGammaIsTwo :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.conservativeShellCGamma
        shellConstants
      ≡
      Schwarzschild.posTwo

    exactShellNumeratorIsFiveThirds :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.exactShellNumerator
        shellConstants
      ≡
      Schwarzschild.posFiveThirds

    formulaStabilityRequestedIsElevenNinths :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.formulaStabilityRequested
        shellConstants
      ≡
      Schwarzschild.posElevenNinths

    repoConservativeFormulaStabilityIsFortyEight :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeFormulaStability
        shellConstants
      ≡
      Schwarzschild.fortyEightN

    ricciContractionRequestedIsFortyEight :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.ricciContractionRequested
        shellConstants
      ≡
      Schwarzschild.fortyEightN

    repoConservativeRicciContractionIsSixHundredForty :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeRicciContraction
        shellConstants
      ≡
      Schwarzschild.sixHundredFortyN

    analyticBlocker :
      GRConcreteFullIntervalChristoffelC0StabilityBlocker

    analyticBlockerIsFullIntervalChristoffelC0Stability :
      analyticBlocker
      ≡
      fullIntervalChristoffelC0StabilityRequired

    exactRemainingC0RicciExtractionBlocker :
      GRConcreteSelectedC0RicciExtractionBlocker

    exactRemainingC0RicciExtractionBlockerIsKernelAndRicci :
      exactRemainingC0RicciExtractionBlocker
      ≡
      christoffelC0StabilityKernelAndRicciExtractionBlocker

    selectedQQConstants :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedQQConstantsAreCanonical :
      selectedQQConstants
      ≡
      Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedQQFormulaStabilityConstantIsFortyEight :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
        selectedQQConstants
      ≡
      48

    selectedQQRicciBoundNumeratorIsFortyEight :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNat
        selectedQQConstants
      ≡
      48

    selectedQQRicciBoundDenominatorIsSixHundredForty :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNat
        selectedQQConstants
      ≡
      640

    conditionalSelectedQQKernelHandoff :
      (kernel : Continuum.SymbolicRationalChristoffelC0StabilityKernel) →
      Continuum.SymbolicRationalChristoffelC0SelectedKernelHandoff kernel

    conditionalSelectedQQKernelHandoffCanonicalProjectionTag :
      Bool

    conditionalSelectedQQKernelHandoffCanonicalProjectionTagIsTrue :
      conditionalSelectedQQKernelHandoffCanonicalProjectionTag
      ≡
      true

    fullIntervalChristoffelC0StabilityRequiredNow :
      Bool

    fullIntervalChristoffelC0StabilityRequiredNowIsTrue :
      fullIntervalChristoffelC0StabilityRequiredNow
      ≡
      true

    fullIntervalChristoffelC0StabilityProvedHere :
      Bool

    fullIntervalChristoffelC0StabilityProvedHereIsFalse :
      fullIntervalChristoffelC0StabilityProvedHere
      ≡
      false

    continuumKernelSurfaceImportedHere :
      Bool

    continuumKernelSurfaceImportedHereIsTrue :
      continuumKernelSurfaceImportedHere
      ≡
      true

    christoffelC0KernelProvidedHere :
      Bool

    christoffelC0KernelProvidedHereIsFalse :
      christoffelC0KernelProvidedHere
      ≡
      false

    ricciExtractionTheoremProvidedHere :
      Bool

    ricciExtractionTheoremProvidedHereIsFalse :
      ricciExtractionTheoremProvidedHere
      ≡
      false

    ricciExtractionBlockedUntilKernelConnectionErrorBound :
      Bool

    ricciExtractionBlockedUntilKernelConnectionErrorBoundIsTrue :
      ricciExtractionBlockedUntilKernelConnectionErrorBound
      ≡
      true

    continuumBlockerStatement :
      String

    projectionBoundary :
      List String

canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt =
  record
    { selectedKoszulHandoff =
        canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff
    ; selectedTorsionIsLocalOnly =
        true
    ; selectedTorsionIsLocalOnlyIsTrue =
        refl
    ; selectedMetricCompatibilityIsLocalOnly =
        true
    ; selectedMetricCompatibilityIsLocalOnlyIsTrue =
        refl
    ; selectedChristoffelFormIsPointTableOnly =
        true
    ; selectedChristoffelFormIsPointTableOnlyIsTrue =
        refl
    ; shellSupremumBounds =
        Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt
    ; shellSupremumBoundsAreCanonical =
        refl
    ; shellParameters =
        Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt
    ; shellParametersAreCanonical =
        refl
    ; shellConstants =
        Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; shellConstantsAreCanonical =
        refl
    ; shellRsIsTwo =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRsIsTwo
          Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt
    ; shellRMinIsThree =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMinIsThree
          Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt
    ; shellRMaxIsThree =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMaxIsThree
          Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt
    ; shellDeltaIsOne =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellDeltaIsOne
          Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt
    ; tightMaxAbsDrGammaIsOne =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.tightMaxAbsDrGammaIsOne
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; conservativeShellCGammaIsTwo =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.conservativeShellCGammaIsTwo
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; exactShellNumeratorIsFiveThirds =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.exactShellNumeratorIsFiveThirds
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; formulaStabilityRequestedIsElevenNinths =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.formulaStabilityRequestedIsElevenNinths
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; repoConservativeFormulaStabilityIsFortyEight =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeFormulaStabilityIsFortyEight
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; ricciContractionRequestedIsFortyEight =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.ricciContractionRequestedIsFortyEight
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; repoConservativeRicciContractionIsSixHundredForty =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeRicciContractionIsSixHundredForty
          Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt
    ; analyticBlocker =
        fullIntervalChristoffelC0StabilityRequired
    ; analyticBlockerIsFullIntervalChristoffelC0Stability =
        refl
    ; exactRemainingC0RicciExtractionBlocker =
        christoffelC0StabilityKernelAndRicciExtractionBlocker
    ; exactRemainingC0RicciExtractionBlockerIsKernelAndRicci =
        refl
    ; selectedQQConstants =
        Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedQQConstantsAreCanonical =
        refl
    ; selectedQQFormulaStabilityConstantIsFortyEight =
        Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNatIs48
          Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedQQRicciBoundNumeratorIsFortyEight =
        Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNatIs48
          Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedQQRicciBoundDenominatorIsSixHundredForty =
        Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNatIs640
          Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; conditionalSelectedQQKernelHandoff =
        Continuum.canonicalSymbolicRationalChristoffelC0SelectedKernelHandoff
    ; conditionalSelectedQQKernelHandoffCanonicalProjectionTag =
        true
    ; conditionalSelectedQQKernelHandoffCanonicalProjectionTagIsTrue =
        refl
    ; fullIntervalChristoffelC0StabilityRequiredNow =
        true
    ; fullIntervalChristoffelC0StabilityRequiredNowIsTrue =
        refl
    ; fullIntervalChristoffelC0StabilityProvedHere =
        false
    ; fullIntervalChristoffelC0StabilityProvedHereIsFalse =
        refl
    ; continuumKernelSurfaceImportedHere =
        true
    ; continuumKernelSurfaceImportedHereIsTrue =
        refl
    ; christoffelC0KernelProvidedHere =
        false
    ; christoffelC0KernelProvidedHereIsFalse =
        refl
    ; ricciExtractionTheoremProvidedHere =
        false
    ; ricciExtractionTheoremProvidedHereIsFalse =
        refl
    ; ricciExtractionBlockedUntilKernelConnectionErrorBound =
        true
    ; ricciExtractionBlockedUntilKernelConnectionErrorBoundIsTrue =
        refl
    ; continuumBlockerStatement =
        "Full interval Christoffel C0 stability and Ricci extraction remain blocked until an external SymbolicRationalChristoffelC0StabilityKernel supplies formula stability and connectionErrorBound extraction"
    ; projectionBoundary =
        "Consumes selectedKoszulHandoff = canonicalGRConcreteSelectedSchwarzschildLeviCivitaKoszulHandoff"
        ∷ "Consumes shellSupremumBounds = Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt"
        ∷ "Consumes shellParameters = Schwarzschild.canonicalSchwarzschildShellSupremumParameterReceipt"
        ∷ "Consumes shellConstants = Schwarzschild.canonicalSchwarzschildShellSupremumConstantReceipt"
        ∷ "Consumes selectedQQConstants = Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt"
        ∷ "Exposes conditionalSelectedQQKernelHandoff only as a function of an external SymbolicRationalChristoffelC0StabilityKernel"
        ∷ "Named shell parameter projections: shellRsIsTwo, shellRMinIsThree, shellRMaxIsThree, shellDeltaIsOne"
        ∷ "Named shell constant projections: tightMaxAbsDrGammaIsOne, conservativeShellCGammaIsTwo, exactShellNumeratorIsFiveThirds, formulaStabilityRequestedIsElevenNinths"
        ∷ "Named conservative projections: repoConservativeFormulaStabilityIsFortyEight, ricciContractionRequestedIsFortyEight, repoConservativeRicciContractionIsSixHundredForty"
        ∷ "Named QQ projections: selectedQQFormulaStabilityConstantIsFortyEight, selectedQQRicciBoundNumeratorIsFortyEight, selectedQQRicciBoundDenominatorIsSixHundredForty"
        ∷ "The exact remaining blocker is christoffelC0StabilityKernelAndRicciExtractionBlocker; no kernel inhabitant or Ricci extraction theorem is provided here"
        ∷ []
    }

grConcreteSelectedLeviCivitaAnalyticBlockerRequiresFullIntervalC0 :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.analyticBlocker
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  fullIntervalChristoffelC0StabilityRequired
grConcreteSelectedLeviCivitaAnalyticBlockerRequiresFullIntervalC0 =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerC0NotProvedHere :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.fullIntervalChristoffelC0StabilityProvedHere
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  false
grConcreteSelectedLeviCivitaAnalyticBlockerC0NotProvedHere =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerTorsionIsLocalOnly :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedTorsionIsLocalOnly
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  true
grConcreteSelectedLeviCivitaAnalyticBlockerTorsionIsLocalOnly =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerMetricCompatibilityIsLocalOnly :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedMetricCompatibilityIsLocalOnly
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  true
grConcreteSelectedLeviCivitaAnalyticBlockerMetricCompatibilityIsLocalOnly =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerFormulaStabilityBudgetIsFortyEight :
  Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeFormulaStability
    (GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.shellConstants
      canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt)
  ≡
  Schwarzschild.fortyEightN
grConcreteSelectedLeviCivitaAnalyticBlockerFormulaStabilityBudgetIsFortyEight =
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.repoConservativeFormulaStabilityIsFortyEight
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt

grConcreteSelectedLeviCivitaAnalyticBlockerExactC0RicciExtractionBlocker :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.exactRemainingC0RicciExtractionBlocker
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  christoffelC0StabilityKernelAndRicciExtractionBlocker
grConcreteSelectedLeviCivitaAnalyticBlockerExactC0RicciExtractionBlocker =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerSelectedQQConstantsAreCanonical :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQConstants
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
grConcreteSelectedLeviCivitaAnalyticBlockerSelectedQQConstantsAreCanonical =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerQQFormulaStabilityConstantIsFortyEight :
  Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
    (GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQConstants
      canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt)
  ≡
  48
grConcreteSelectedLeviCivitaAnalyticBlockerQQFormulaStabilityConstantIsFortyEight =
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQFormulaStabilityConstantIsFortyEight
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt

grConcreteSelectedLeviCivitaAnalyticBlockerQQRicciBoundNumeratorIsFortyEight :
  Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNat
    (GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQConstants
      canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt)
  ≡
  48
grConcreteSelectedLeviCivitaAnalyticBlockerQQRicciBoundNumeratorIsFortyEight =
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQRicciBoundNumeratorIsFortyEight
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt

grConcreteSelectedLeviCivitaAnalyticBlockerQQRicciBoundDenominatorIsSixHundredForty :
  Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNat
    (GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQConstants
      canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt)
  ≡
  640
grConcreteSelectedLeviCivitaAnalyticBlockerQQRicciBoundDenominatorIsSixHundredForty =
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.selectedQQRicciBoundDenominatorIsSixHundredForty
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt

grConcreteSelectedLeviCivitaAnalyticBlockerConditionalKernelHandoffCanonicalProjectionTag :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.conditionalSelectedQQKernelHandoffCanonicalProjectionTag
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  true
grConcreteSelectedLeviCivitaAnalyticBlockerConditionalKernelHandoffCanonicalProjectionTag =
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.conditionalSelectedQQKernelHandoffCanonicalProjectionTagIsTrue
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt

grConcreteSelectedLeviCivitaAnalyticBlockerKernelNotProvidedHere :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.christoffelC0KernelProvidedHere
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  false
grConcreteSelectedLeviCivitaAnalyticBlockerKernelNotProvidedHere =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerRicciExtractionNotProvidedHere :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.ricciExtractionTheoremProvidedHere
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  false
grConcreteSelectedLeviCivitaAnalyticBlockerRicciExtractionNotProvidedHere =
  refl

grConcreteSelectedLeviCivitaAnalyticBlockerRicciExtractionBlockedUntilKernel :
  GRConcreteSelectedLeviCivitaAnalyticBlockerReceipt.ricciExtractionBlockedUntilKernelConnectionErrorBound
    canonicalGRConcreteSelectedLeviCivitaAnalyticBlockerReceipt
  ≡
  true
grConcreteSelectedLeviCivitaAnalyticBlockerRicciExtractionBlockedUntilKernel =
  refl
