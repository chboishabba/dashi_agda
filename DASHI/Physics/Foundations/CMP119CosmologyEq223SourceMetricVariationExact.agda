{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

record Eq223SourceMetricVariationRealization
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    (Configuration : Set)
    (scale : Nat)
    : Set₁ where
  field
    wilsonMetricVariation :
      WilsonTerm →
      Wilson.ClassicalWilsonTenMetricVariation Configuration

    regularMetricVariation :
      SmallFieldTerm →
      K.SymmetricTensorComponent4 →
      Configuration → ℚ

    rOperationMetricVariation :
      RTerm →
      K.SymmetricTensorComponent4 →
      Configuration → ℚ

    boundaryMetricVariation :
      BoundaryTerm →
      K.SymmetricTensorComponent4 →
      Configuration → ℚ

    vacuumMetricVariation :
      Vacuum →
      K.SymmetricTensorComponent4 →
      ℚ

    referenceMeasureLogVariation :
      K.SymmetricTensorComponent4 →
      Configuration → ℚ

open Eq223SourceMetricVariationRealization public

sourceCompleteFiniteMetricVariation :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  Eq223SourceMetricVariationRealization source Configuration scale →
  Source.CompleteFiniteMetricVariation Configuration
sourceCompleteFiniteMetricVariation
    {source = source} {scale = scale} realization = record
  { Source.CompleteFiniteMetricVariation.wilson =
      wilsonMetricVariation realization
        (Raw.wilsonActionTerm source scale)
  ; Source.CompleteFiniteMetricVariation.regularVariation =
      regularMetricVariation realization
        (Raw.regularSmallFieldTerm source scale)
  ; Source.CompleteFiniteMetricVariation.rOperationVariation =
      rOperationMetricVariation realization
        (Raw.rOperationTerm source scale)
  ; Source.CompleteFiniteMetricVariation.boundaryVariation =
      boundaryMetricVariation realization
        (Raw.boundaryTerm source scale)
  ; Source.CompleteFiniteMetricVariation.vacuumVariation =
      λ component _ →
        vacuumMetricVariation realization
          (Raw.vacuumEnergy source scale)
          component
  ; Source.CompleteFiniteMetricVariation.referenceMeasureLogVariation =
      referenceMeasureLogVariation realization
  }

regularVariationIsLiteralEq223E :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale source}
    (realization :
      Eq223SourceMetricVariationRealization
        {Density} {Background} {Fluctuation}
        {Action} {WilsonTerm} {SmallFieldTerm}
        {RTerm} {BoundaryTerm} {Vacuum}
        source Configuration scale)
    component configuration →
  Source.regularVariation
    (sourceCompleteFiniteMetricVariation realization)
    component configuration
  ≡
  regularMetricVariation realization
    (Raw.regularSmallFieldTerm source scale)
    component configuration
regularVariationIsLiteralEq223E realization component configuration = refl

rOperationVariationIsLiteralEq223R :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale source}
    (realization :
      Eq223SourceMetricVariationRealization
        {Density} {Background} {Fluctuation}
        {Action} {WilsonTerm} {SmallFieldTerm}
        {RTerm} {BoundaryTerm} {Vacuum}
        source Configuration scale)
    component configuration →
  Source.rOperationVariation
    (sourceCompleteFiniteMetricVariation realization)
    component configuration
  ≡
  rOperationMetricVariation realization
    (Raw.rOperationTerm source scale)
    component configuration
rOperationVariationIsLiteralEq223R realization component configuration = refl

boundaryVariationIsLiteralEq223B :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale source}
    (realization :
      Eq223SourceMetricVariationRealization
        {Density} {Background} {Fluctuation}
        {Action} {WilsonTerm} {SmallFieldTerm}
        {RTerm} {BoundaryTerm} {Vacuum}
        source Configuration scale)
    component configuration →
  Source.boundaryVariation
    (sourceCompleteFiniteMetricVariation realization)
    component configuration
  ≡
  boundaryMetricVariation realization
    (Raw.boundaryTerm source scale)
    component configuration
boundaryVariationIsLiteralEq223B realization component configuration = refl

vacuumVariationIsLiteralEq223V :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale source}
    (realization :
      Eq223SourceMetricVariationRealization
        {Density} {Background} {Fluctuation}
        {Action} {WilsonTerm} {SmallFieldTerm}
        {RTerm} {BoundaryTerm} {Vacuum}
        source Configuration scale)
    component configuration →
  Source.vacuumVariation
    (sourceCompleteFiniteMetricVariation realization)
    component configuration
  ≡
  vacuumMetricVariation realization
    (Raw.vacuumEnergy source scale)
    component
vacuumVariationIsLiteralEq223V realization component configuration = refl

vacuumDiagonalTraceIndependentOfConfiguration :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
      Configuration scale source}
    (realization :
      Eq223SourceMetricVariationRealization
        {Density} {Background} {Fluctuation}
        {Action} {WilsonTerm} {SmallFieldTerm}
        {RTerm} {BoundaryTerm} {Vacuum}
        source Configuration scale)
    (left right : Configuration) →
  Sector.vacuumDiagonalTrace
    (sourceCompleteFiniteMetricVariation realization) left
  ≡
  Sector.vacuumDiagonalTrace
    (sourceCompleteFiniteMetricVariation realization) right
vacuumDiagonalTraceIndependentOfConfiguration realization left right = refl

anonymousERBVCallbacksEliminated : Bool
anonymousERBVCallbacksEliminated = true

vacuumConfigurationIndependenceStructural : Bool
vacuumConfigurationIndependenceStructural = true
