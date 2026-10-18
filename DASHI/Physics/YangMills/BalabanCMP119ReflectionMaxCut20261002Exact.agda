{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ReflectionMaxCut20261002Exact where

------------------------------------------------------------------------
-- CMP119 REFLECTION-POSITIVITY SOURCE MAX-CUT
--
-- Primary source:
-- T. Balaban, "Convergent Renormalization Expansions for Lattice Gauge
-- Theories", CMP 119 (1988), 243--285, DOI 10.1007/BF01217741.
--
-- This owner records only what the existing source-native repository objects
-- justify for the finite OS/reflection audit.
--
-- Equation (2.23) keeps four non-Wilson source sectors distinct:
--   E_k, R_k, B_k, and vacuum energy.
--
-- The vacuum coordinate is a scale-indexed Vacuum object, not a function of a
-- gauge configuration.  Hence its canonical literal realization is constant
-- on configurations.  This does NOT by itself prove that an independently
-- chosen action evaluator realizes the source vacuum contribution by that
-- constant; that same-object evaluator/action identification remains explicit.
--
-- For B_k the source-backed repository owns localization, analyticity,
-- gauge invariance and exponential decay.  None of those predicates is
-- reflection positivity.  E_k and R_k likewise have their own source
-- localized-analytic classes.  Therefore the surviving finite-RP certificate
-- leaves are exactly E, R and B; no decay/smallness predicate is promoted to a
-- PSD/reflected-half certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119CMP122BoundaryReinjectionSourceExact as Boundary

data CMP119ReflectionSector : Set where
  regularE rOperation boundaryB vacuumV : CMP119ReflectionSector

data ReflectionAuditStatus : Set where
  reflectedHalfClosed
  physicalCertificateOpen : ReflectionAuditStatus

reflectionAuditStatus : CMP119ReflectionSector → ReflectionAuditStatus
reflectionAuditStatus regularE = physicalCertificateOpen
reflectionAuditStatus rOperation = physicalCertificateOpen
reflectionAuditStatus boundaryB = physicalCertificateOpen
reflectionAuditStatus vacuumV = reflectedHalfClosed

survivingResidualReflectionLeaves : List CMP119ReflectionSector
survivingResidualReflectionLeaves =
  regularE ∷ rOperation ∷ boundaryB ∷ []

vacuumRemovedFromCrossPlaneCut :
  reflectionAuditStatus vacuumV ≡ reflectedHalfClosed
vacuumRemovedFromCrossPlaneCut = refl

regularEStillPhysical :
  reflectionAuditStatus regularE ≡ physicalCertificateOpen
regularEStillPhysical = refl

rOperationStillPhysical :
  reflectionAuditStatus rOperation ≡ physicalCertificateOpen
rOperationStillPhysical = refl

boundaryBStillPhysical :
  reflectionAuditStatus boundaryB ≡ physicalCertificateOpen
boundaryBStillPhysical = refl

------------------------------------------------------------------------
-- Canonical constant realization of the SOURCE vacuum coordinate.
------------------------------------------------------------------------

sourceVacuumConstant :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) →
  Nat → Configuration → Vacuum
sourceVacuumConstant source scale configuration =
  Raw.vacuumEnergy source scale

sourceVacuumConstantIndependent :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    scale (left right : Configuration) →
  sourceVacuumConstant source scale left
  ≡ sourceVacuumConstant source scale right
sourceVacuumConstantIndependent source scale left right = refl

------------------------------------------------------------------------
-- Boundary source facts are locality/analyticity facts, not RP certificates.
------------------------------------------------------------------------

boundaryTermAnalytic :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    (sourceClass :
      Boundary.CMP119BoundaryTermClass
        Scale Polymer BoundaryTerm AnalyticDomain)
    scale polymer term →
  Boundary.AnalyticOn sourceClass term
    (Boundary.domain sourceClass scale polymer)
boundaryTermAnalytic sourceClass scale polymer term =
  Boundary.analyticOnInductiveDomain sourceClass scale polymer term

boundaryTermGaugeInvariant :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    (sourceClass :
      Boundary.CMP119BoundaryTermClass
        Scale Polymer BoundaryTerm AnalyticDomain)
    scale polymer term →
  Boundary.GaugeInvariant sourceClass term
boundaryTermGaugeInvariant sourceClass scale polymer term =
  Boundary.gaugeInvariant sourceClass scale polymer term

boundaryTermExponentiallyLocalized :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    (sourceClass :
      Boundary.CMP119BoundaryTermClass
        Scale Polymer BoundaryTerm AnalyticDomain)
    scale polymer term →
  Boundary.ExponentiallyLocalized sourceClass scale polymer term
boundaryTermExponentiallyLocalized sourceClass scale polymer term =
  Boundary.exponentiallyLocalized sourceClass scale polymer term

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

boundaryLocalizationIsNotRecordedAsRP : Bool
boundaryLocalizationIsNotRecordedAsRP = true

regularLocalizationIsNotRecordedAsRP : Bool
regularLocalizationIsNotRecordedAsRP = true

rOperationLocalizationIsNotRecordedAsRP : Bool
rOperationLocalizationIsNotRecordedAsRP = true

boundaryLocalizationIsNotRecordedAsRPIsTrue :
  boundaryLocalizationIsNotRecordedAsRP ≡ true
boundaryLocalizationIsNotRecordedAsRPIsTrue = refl

cmp119ReflectionMaxCutCompilerLevel : ProofLevel
cmp119ReflectionMaxCutCompilerLevel = machineChecked

-- Same-object physical leaves still required:
--   * identify the selected action evaluator's vacuum contribution with the
--     canonical constant realization above;
--   * construct an actual reflected-half or PSD cross-plane certificate for
--     E_k, R_k and B_k on the selected reflection boundary carrier.
cmp119VacuumActionEvaluatorConstantIdentificationLevel : ProofLevel
cmp119VacuumActionEvaluatorConstantIdentificationLevel = conditional

cmp119ERBReflectionCertificateLevel : ProofLevel
cmp119ERBReflectionCertificateLevel = conditional
