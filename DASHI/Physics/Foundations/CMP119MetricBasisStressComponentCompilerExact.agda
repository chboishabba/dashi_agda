{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as Rat using (ℚ)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119

------------------------------------------------------------------------
-- CMP119 METRIC-BASIS -> 4x4 RATIONAL STRESS COMPONENTS
--
-- R119 already owns a rational readout for the exact canonical metric first
-- variation / selected CMP119 stress insertion.  Therefore no new stress law is
-- needed to obtain tensor components: choose sixteen admissible metric
-- perturbations representing the coordinate basis h^(mu nu), and evaluate the
-- existing stress pairing/readout on them.
------------------------------------------------------------------------

record MetricBasis16
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity) : Set₁ where
  field
    basisPerturbation :
      Flat.Axis4 → Flat.Axis4 →
      Domain.MetricPerturbation domain

    basisAdmissible :
      ∀ a b →
      Domain.AdmissibleMetricPerturbation domain
        (basisPerturbation a b)

open MetricBasis16 public

record RationalStressPairingReadout
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    (representation : StressRep.CanonicalMetricStressRepresentation domain) : Set₁ where
  field
    pairingToRational :
      StressRep.PairingScalar representation →
      ℚ

open RationalStressPairingReadout public

cmp119MetricBasisComponent :
  ∀ {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain} →
  MetricBasis16 domain →
  RationalStressPairingReadout representation →
  StressRep.StressTensor representation →
  Flat.Axis4 → Flat.Axis4 →
  ℚ
cmp119MetricBasisComponent basis readout stress a b =
  pairingToRational readout
    (StressRep.stressMetricPairing representation stress
      (basisPerturbation basis a b))

cmp119MetricBasisEvaluator :
  ∀ {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain} →
  MetricBasis16 domain →
  RationalStressPairingReadout representation →
  Cut.CMP119RationalStressComponentEvaluator
    (StressRep.StressTensor representation)
cmp119MetricBasisEvaluator basis readout = record
  { Cut.CMP119RationalStressComponentEvaluator.component =
      cmp119MetricBasisComponent basis readout
  }

record R119MetricBasisComponentWeld
    {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate} 
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate)
    (basis : MetricBasis16 domain) : Set₁ where
  field
    background : Chain.Background activity

    pairingReadout :
      RationalStressPairingReadout representation

    pairingReadoutIsR119Readout :
      ∀ scalar →
      pairingToRational pairingReadout scalar
      ≡ R119.readoutToRational selected scalar

open R119MetricBasisComponentWeld public

r119BasisComponentIsSelectedCMP119Insertion :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate}
    {selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate}
    {basis : MetricBasis16 domain} →
  R119MetricBasisComponentWeld selected basis →
  ∀ a b →
  cmp119MetricBasisComponent
      basis
      (pairingReadout weld)
      (StressRep.stressTensor representation)
      a b
  ≡
  R119.readoutToRational selected
    (StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation)
      (basisPerturbation basis a b))
r119BasisComponentIsSelectedCMP119Insertion
    {representation = representation} {basis = basis} weld a b =
  pairingReadoutIsR119Readout weld
    (StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation)
      (basisPerturbation basis a b))

secondStressRepresentationNeededForComponents : Bool
secondStressRepresentationNeededForComponents = false

secondStressRepresentationNeededForComponentsIsFalse :
  secondStressRepresentationNeededForComponents ≡ false
secondStressRepresentationNeededForComponentsIsFalse = refl

metricBasis16StillNeedsPhysicalCoordinateIdentification : Bool
metricBasis16StillNeedsPhysicalCoordinateIdentification = true

metricBasis16StillNeedsPhysicalCoordinateIdentificationIsTrue :
  metricBasis16StillNeedsPhysicalCoordinateIdentification ≡ true
metricBasis16StillNeedsPhysicalCoordinateIdentificationIsTrue = refl
