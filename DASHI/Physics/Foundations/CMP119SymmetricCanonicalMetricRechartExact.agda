{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact where

open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- RECHART THE CANONICAL METRIC DOMAIN ON THE TEN-SLOT SYMMETRIC CARRIER
--
-- An existing SymmetricMetricBasisRealization already supplies, for every
-- symmetric tensor slot, an admissible perturbation in the original Round106
-- domain.  Pull the whole Round106 domain/representation/R119 weld back along
-- that map.
--
-- The resulting selected source has MetricPerturbation definitionally equal to
-- SymmetricTensorComponent4.  No inverse map and no ten separate coordinate
-- equalities are needed.
------------------------------------------------------------------------

module _
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (realization : Basis.SymmetricMetricBasisRealization domain)
  where

  symmetricDomain :
    Domain.CanonicalMetricSourceDomain Scale Volume activity
  symmetricDomain = record
    { Domain.CanonicalMetricSourceDomain.demands =
        Domain.demands domain
    ; Domain.CanonicalMetricSourceDomain.radiusData =
        Domain.radiusData domain
    ; Domain.CanonicalMetricSourceDomain.radiusIsCanonical =
        Domain.radiusIsCanonical domain
    ; Domain.CanonicalMetricSourceDomain.MetricPerturbation =
        K.SymmetricTensorComponent4
    ; Domain.CanonicalMetricSourceDomain.metricPerturbationNorm =
        λ component →
          Domain.metricPerturbationNorm domain
            (Basis.componentPerturbation realization component)
    ; Domain.CanonicalMetricSourceDomain.AdmissibleMetricPerturbation =
        λ component →
          Domain.AdmissibleMetricPerturbation domain
            (Basis.componentPerturbation realization component)
    ; Domain.CanonicalMetricSourceDomain.admissibleMetricPerturbationBelowRadius =
        λ component admissible →
          Domain.admissibleMetricPerturbationBelowRadius
            domain
            (Basis.componentPerturbation realization component)
            admissible
    ; Domain.CanonicalMetricSourceDomain.metricPerturbationToBackgroundTangent =
        λ background component →
          Domain.metricPerturbationToBackgroundTangent
            domain background
            (Basis.componentPerturbation realization component)
    ; Domain.CanonicalMetricSourceDomain.SourceTangentInside =
        Domain.SourceTangentInside domain
    ; Domain.CanonicalMetricSourceDomain.admittedMetricTangentInside =
        λ scale volume background component admissible →
          Domain.admittedMetricTangentInside
            domain scale volume background
            (Basis.componentPerturbation realization component)
            admissible
    }

  symmetricMetricCarrierIsTenSlot :
    Domain.MetricPerturbation symmetricDomain
    ≡ K.SymmetricTensorComponent4
  symmetricMetricCarrierIsTenSlot = refl

  symmetricRepresentation :
    StressRep.CanonicalMetricStressRepresentation domain →
    StressRep.CanonicalMetricStressRepresentation symmetricDomain
  symmetricRepresentation representation = record
    { StressRep.CanonicalMetricStressRepresentation.StressTensor =
        StressRep.StressTensor representation
    ; StressRep.CanonicalMetricStressRepresentation.PairingScalar =
        StressRep.PairingScalar representation
    ; StressRep.CanonicalMetricStressRepresentation.stressTensor =
        StressRep.stressTensor representation
    ; StressRep.CanonicalMetricStressRepresentation.firstVariationReadout =
        StressRep.firstVariationReadout representation
    ; StressRep.CanonicalMetricStressRepresentation.stressMetricPairing =
        λ stress component →
          StressRep.stressMetricPairing representation
            stress
            (Basis.componentPerturbation realization component)
    ; StressRep.CanonicalMetricStressRepresentation.firstVariationRepresentedByStress =
        λ background component admissible →
          StressRep.firstVariationRepresentedByStress
            representation
            background
            (Basis.componentPerturbation realization component)
            admissible
    }

module _
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (realization : Basis.SymmetricMetricBasisRealization domain)
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
  where

  rechartedDomain =
    symmetricDomain domain realization

  rechartedRepresentation =
    symmetricRepresentation domain realization representation

  rechartedSelectedStress :
    R119.CanonicalMetricSelectedStressWeld
      rechartedDomain rechartedRepresentation coordinate
  rechartedSelectedStress = record
    { R119.CanonicalMetricSelectedStressWeld.readoutToRational =
        R119.readoutToRational selected
    ; R119.CanonicalMetricSelectedStressWeld.normalizedSource =
        λ background component →
          R119.normalizedSource selected background
            (Basis.componentPerturbation realization component)
    ; R119.CanonicalMetricSelectedStressWeld.metricFirstVariationCrossNumerator =
        λ background component →
          R119.metricFirstVariationCrossNumerator selected background
            (Basis.componentPerturbation realization component)
    ; R119.CanonicalMetricSelectedStressWeld.localInsertionNumerator =
        R119.localInsertionNumerator selected
    ; R119.CanonicalMetricSelectedStressWeld.finiteFirstVariationReadoutIsCrossNumerator =
        λ background component admissible →
          R119.finiteFirstVariationReadoutIsCrossNumerator
            selected background
            (Basis.componentPerturbation realization component)
            admissible
    ; R119.CanonicalMetricSelectedStressWeld.metricVariationIsNormalizedCrossNumerator =
        λ background component →
          R119.metricVariationIsNormalizedCrossNumerator
            selected background
            (Basis.componentPerturbation realization component)
    ; R119.CanonicalMetricSelectedStressWeld.connectedInsertionIsSelectedCMP119StressInsertion =
        λ background component →
          R119.connectedInsertionIsSelectedCMP119StressInsertion
            selected background
            (Basis.componentPerturbation realization component)
    }

  rechartedNormalizedSource :
    Chain.Background activity →
    K.SymmetricTensorComponent4 →
    R116.NormalizedSourceDerivativeCrossData
  rechartedNormalizedSource =
    R119.normalizedSource rechartedSelectedStress
