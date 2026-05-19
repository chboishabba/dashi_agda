module DASHI.Physics.Closure.GRConcreteLeviCivita where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G3SelectedCarrierInstance as G3Sel
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GR
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
