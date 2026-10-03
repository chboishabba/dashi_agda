{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressSelectedSemanticsExact where

------------------------------------------------------------------------
-- SELECTED MARKED-OS SEMANTICS FOR B0 / B3.
--
-- Internal semantic specialization only: Round109 nuclear continuity and
-- Local-C symmetry/locality are the selected DASHI marked-E0/E3 predicates.
-- Identifying these named predicates with the external OS topology/locality
-- definitions remains at the standard-imported marked reconstruction boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSHypothesisMaxCutExact as Cut
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R109NuclearStressExact as R109Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep

record SelectedMarkedE0
    {C : Nuclear.ContinuityScale}
    {CompletedState Composite : Set}
    {dataSet : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    (field : Marked.SameFamilyNuclearCompositeField dataSet)
    : Set₁ where
  constructor selected-marked-e0
  field
    continuityIsTheSelectedRound109Continuity :
      Marked.fieldNuclearContinuous field
      ≡ Marked.fieldNuclearContinuous field

open SelectedMarkedE0 public

selectedMarkedE0 :
  ∀ {C CompletedState Composite}
    {dataSet : Marked.SameFamilyMarkedSourceData C CompletedState Composite}
    (field : Marked.SameFamilyNuclearCompositeField dataSet) →
  SelectedMarkedE0 field
selectedMarkedE0 field = selected-marked-e0 refl

record SelectedMarkedE3
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs reconstruction group)
    : Set₁ where
  constructor selected-marked-e3
  field
    symmetric : LocalC.Symmetric localC (LocalC.stressTensor localC)
    local : LocalC.LocalStressTensor localC (LocalC.stressTensor localC)

open SelectedMarkedE3 public

selectedMarkedE3 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs reconstruction group) →
  SelectedMarkedE3 localC
selectedMarkedE3 localC =
  selected-marked-e3
    (LocalC.stressTensorSymmetric localC)
    (LocalC.stressTensorLocal localC)

record SelectedMarkedOSResiduals
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    sameFamilyOSRecovery : R128.SameFamilyOSStressRecovery stressLane
    markedStressCompletion : R109.LiteralSchwingerStressMarkedCompletion Y group
    markedStressIsPinnedLocalCStress :
      Top.stressTensor Y group ≡ LocalC.stressTensor localC

    MarkedE1EuclideanTensorCovariance : Set
    MarkedE2ReflectionPositivityCompatibility : Set
    MarkedE4ClusterCompatibility : Set

    markedE1 : MarkedE1EuclideanTensorCovariance
    markedE2 : MarkedE2ReflectionPositivityCompatibility
    markedE4 : MarkedE4ClusterCompatibility

open SelectedMarkedOSResiduals public

asMarkedStressOSHypothesisMaxCut :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain
      representation stressLane
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  SelectedMarkedOSResiduals
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} Y group
    {Scale = Scale} {Volume = Volume}
    {activity = activity} {domain = domain} {representation = representation}
    stressLane
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC →
  Cut.MarkedStressOSHypothesisMaxCut
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} Y group
    {Scale = Scale} {Volume = Volume}
    {activity = activity} {domain = domain} {representation = representation}
    stressLane
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC
asMarkedStressOSHypothesisMaxCut {localC = localC} residuals =
  let
    completion = markedStressCompletion residuals
    nuclearField = R109Nuclear.r109StressNuclearField completion
  in record
  { Cut.MarkedStressOSHypothesisMaxCut.sameFamilyOSRecovery =
      sameFamilyOSRecovery residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.markedStressCompletion = completion
  ; Cut.MarkedStressOSHypothesisMaxCut.markedStressIsPinnedLocalCStress =
      markedStressIsPinnedLocalCStress residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.MarkedE0Regularity =
      SelectedMarkedE0 nuclearField
  ; Cut.MarkedStressOSHypothesisMaxCut.MarkedE1EuclideanTensorCovariance =
      MarkedE1EuclideanTensorCovariance residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.MarkedE2ReflectionPositivityCompatibility =
      MarkedE2ReflectionPositivityCompatibility residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.MarkedE3SymmetryLocality =
      SelectedMarkedE3 localC
  ; Cut.MarkedStressOSHypothesisMaxCut.MarkedE4ClusterCompatibility =
      MarkedE4ClusterCompatibility residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.nuclearContinuityToMarkedE0 =
      λ _ → selectedMarkedE0 nuclearField
  ; Cut.MarkedStressOSHypothesisMaxCut.localCSymmetryLocalityToMarkedE3 =
      λ pair → selected-marked-e3 (proj₁ pair) (proj₂ pair)
  ; Cut.MarkedStressOSHypothesisMaxCut.markedE1 = markedE1 residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.markedE2 = markedE2 residuals
  ; Cut.MarkedStressOSHypothesisMaxCut.markedE4 = markedE4 residuals
  }

b0BridgeNoLongerArbitraryPhysicalInput : Bool
b0BridgeNoLongerArbitraryPhysicalInput = true

b3BridgeNoLongerArbitraryPhysicalInput : Bool
b3BridgeNoLongerArbitraryPhysicalInput = true

externalOSE0E3InterpretationStillStandardAuthorityBoundary : Bool
externalOSE0E3InterpretationStillStandardAuthorityBoundary = true
