{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityF2StressSameLiteralEndpointExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentExact as StressAttach
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119GRQFTStressExportExact as StressExport

------------------------------------------------------------------------
-- AG-S2 / SELECTED F^2 AND GRQFT STRESS ON ONE LITERAL C ENDPOINT
--
-- No second Local-C package is allowed.  The selected F^2 local operator and
-- the GRQFT stress tensor are taken from the SAME concrete pinned Local-C input.
-- Stress/Hamiltonian same-object transport is already owned by the existing
-- literal stress attachment.  The sole new curvature payment is the selected
-- operator equality below.
------------------------------------------------------------------------

record SelectedF2LiteralStressEndpoint
    {Carriers : Top.LiteralYangMillsCarriers}
    {Semantics : Top.LiteralYangMillsSemantics Carriers}
    (Y : Top.LiteralYangMillsConstruction Carriers Semantics)
    (group : Top.CompactSimpleGroup Carriers)
    {X Configuration Position OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup Carriers)
        X Configuration Position
        (Top.CurvaturePolynomial Carriers)
        (Top.LocalOperator Carriers)
        OPECoefficient
        (Top.StressTensor Carriers)
        Hilbert Vector
        (Top.Hamiltonian Carriers)
        Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs reconstruction group) : Set₁ where
  field
    stressAttachment :
      StressAttach.PinnedCMP119LiteralStressAttachment
        Y group inputs

    selectedF2Polynomial :
      Top.CurvaturePolynomial Carriers

    selectedLocalCF2IsLiteralCurvatureF2 :
      C.localOperator inputs selectedF2Polynomial
      ≡
      Top.curvatureOperator Y group selectedF2Polynomial

open SelectedF2LiteralStressEndpoint public

selectedEndpointStressIsLiteralStress :
  ∀ {Carriers Semantics Y group
      X Configuration Position OPECoefficient
      Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction inputs}
    (endpoint :
      SelectedF2LiteralStressEndpoint
        {Carriers = Carriers} {Semantics = Semantics}
        Y group
        {X = X} {Configuration = Configuration} {Position = Position}
        {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} {reconstruction = reconstruction}
        inputs) →
  StressExport.qftStressTensor
    (StressExport.exportPinnedCMP119StressEndpoint inputs)
  ≡ Top.stressTensor Y group
selectedEndpointStressIsLiteralStress {inputs = inputs} endpoint =
  StressAttach.cmp119StressIsLiteralStress
    (stressAttachment endpoint)

selectedF2AndStressUseSameConcreteLocalC : Bool
selectedF2AndStressUseSameConcreteLocalC = true

selectedF2LiteralCurvatureEqualityStillRequired : Bool
selectedF2LiteralCurvatureEqualityStillRequired = true

secondStressPackageRequiredForS2 : Bool
secondStressPackageRequiredForS2 = false

selectedF2AndStressUseSameConcreteLocalCIsTrue :
  selectedF2AndStressUseSameConcreteLocalC ≡ true
selectedF2AndStressUseSameConcreteLocalCIsTrue = refl

selectedF2LiteralCurvatureEqualityStillRequiredIsTrue :
  selectedF2LiteralCurvatureEqualityStillRequired ≡ true
selectedF2LiteralCurvatureEqualityStillRequiredIsTrue = refl

secondStressPackageRequiredForS2IsFalse :
  secondStressPackageRequiredForS2 ≡ false
secondStressPackageRequiredForS2IsFalse = refl
