{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityScalarVacuumSourceActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityVacuumConstantSourceBoundaryExact as SourceBoundary

------------------------------------------------------------------------
-- SOURCE-FIRST CMP119 EQ.(2.23) WITH A SCALAR VACUUM CONSTANT
--
-- CMP119Section2SourceNativeState already gives the final Eq.(2.23) vacuum
-- summand its own type parameter `Vacuum`; the primary-source boundary pins
-- Bałaban's description of the vacuum-energy counterterm as a normalization /
-- constant term.  The preferred antigravity adapter therefore instantiates
--
--   Vacuum = ℚ
--
-- rather than reusing LocalizedAction and asking a projector to guess which
-- coordinate is the constant.  The action algebra embeds the scalar explicitly:
--
--   V ↦ irrelevantAction V = localizedAction 0 V.
--
-- This pays the representation/encoding problem by construction and is
-- source-supported at the semantic-role level.  It does NOT identify V with a
-- physical cosmological constant: metric response, gravitational
-- renormalization/calibration, Lorentzian continuation and SI authority remain
-- separate downstream obligations.
------------------------------------------------------------------------

scalarVacuumAssemble :
  ℚ →
  T4.LocalizedAction → T4.LocalizedAction →
  T4.LocalizedAction → T4.LocalizedAction →
  ℚ →
  T4.LocalizedAction
scalarVacuumAssemble coefficient wilson regular r boundary vacuum =
  T4.addLocalizedAction
    (T4.scaleLocalizedAction coefficient wilson)
    (T4.addLocalizedAction regular
      (T4.addLocalizedAction r
        (T4.addLocalizedAction boundary
          (T4.irrelevantAction vacuum))))

scalarVacuumAlgebra :
  Source.CMP119ActionAlgebra
    T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction
    ℚ
scalarVacuumAlgebra = record
  { Source.CMP119ActionAlgebra.assemble = scalarVacuumAssemble }

scalarVacuumAssemblyEmbedsConstantAsIrrelevantAction :
  ∀ coefficient wilson regular r boundary vacuum →
  Source.assemble scalarVacuumAlgebra
    coefficient wilson regular r boundary vacuum
  ≡
  T4.addLocalizedAction
    (T4.scaleLocalizedAction coefficient wilson)
    (T4.addLocalizedAction regular
      (T4.addLocalizedAction r
        (T4.addLocalizedAction boundary
          (T4.irrelevantAction vacuum))))
scalarVacuumAssemblyEmbedsConstantAsIrrelevantAction
  coefficient wilson regular r boundary vacuum = refl

module _ {Density Background Fluctuation : Set} where

  ScalarVacuumCMP119Source : Set₁
  ScalarVacuumCMP119Source =
    Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction
      ℚ

  record ScalarVacuumSourceInstantiation : Set₁ where
    field
      source : ScalarVacuumCMP119Source
      actionAlgebraIsScalarVacuumAlgebra :
        Source.actionAlgebra source ≡ scalarVacuumAlgebra

  open ScalarVacuumSourceInstantiation public

  vacuumConstantAt : ScalarVacuumSourceInstantiation → Nat → ℚ
  vacuumConstantAt instantiation =
    Source.vacuumEnergy (source instantiation)

  sourceEquation223UsesScalarVacuumAssembly :
    (instantiation : ScalarVacuumSourceInstantiation) →
    ∀ scale →
    Source.effectiveAction (source instantiation) scale
    ≡
    scalarVacuumAssemble
      (Source.wilsonCoefficient (source instantiation) scale)
      (Source.wilsonActionTerm (source instantiation) scale)
      (Source.regularSmallFieldTerm (source instantiation) scale)
      (Source.rOperationTerm (source instantiation) scale)
      (Source.boundaryTerm (source instantiation) scale)
      (Source.vacuumEnergy (source instantiation) scale)
  sourceEquation223UsesScalarVacuumAssembly instantiation scale
    rewrite actionAlgebraIsScalarVacuumAlgebra instantiation =
    Source.equation223 (source instantiation) scale

preferredScalarVacuumRepresentationSourceSupported : Bool
preferredScalarVacuumRepresentationSourceSupported =
  SourceBoundary.preferredScalarVacuumRepresentationSourceSupported

vacuumEnergyIsRationalByConstruction : Bool
vacuumEnergyIsRationalByConstruction = true

vacuumAssemblyUsesConstantRemainderCoordinate : Bool
vacuumAssemblyUsesConstantRemainderCoordinate = true

allLocalizedActionVacuumAdapterPreferred : Bool
allLocalizedActionVacuumAdapterPreferred = false

postHocVacuumConstantEncodingReceiptRequiredOnPreferredRoute : Bool
postHocVacuumConstantEncodingReceiptRequiredOnPreferredRoute = false

physicalLambdaIdentifiedByScalarVacuumRepresentationAlone : Bool
physicalLambdaIdentifiedByScalarVacuumRepresentationAlone = false

metricResponsePaidByPrimaryVacuumConstantSourceBoundary : Bool
metricResponsePaidByPrimaryVacuumConstantSourceBoundary =
  SourceBoundary.sourceProvesMetricResponseOfVacuumConstant

record ScalarVacuumSourceActionBoundary : Set where
  constructor scalar-vacuum-source-action-boundary
  field
    sourceSupportsScalarVacuumSemanticRole : Bool
    cmp119VacuumTypedAsIndependentScalar : Bool
    scalarEmbeddedAsConstantActionByConstruction : Bool
    plaquetteProjectorNeededToReadVacuumConstant : Bool
    postHocConstantEncodingEqualityNeededOnPreferredRoute : Bool
    representationAlonePaysGravitationalMetricResponse : Bool

canonicalScalarVacuumSourceActionBoundary : ScalarVacuumSourceActionBoundary
canonicalScalarVacuumSourceActionBoundary =
  scalar-vacuum-source-action-boundary
    true true true false false false
