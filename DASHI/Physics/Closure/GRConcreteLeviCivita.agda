module DASHI.Physics.Closure.GRConcreteLeviCivita where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G3SelectedCarrierInstance as G3Sel
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GR
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML

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
