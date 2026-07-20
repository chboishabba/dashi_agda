module DASHI.Physics.Closure.PhysicsClosureCrossPollinationTheorem where

-- Cross-pollination surface for the current physics programme.
--
-- This file deliberately distinguishes three different theorem states:
--
-- 1. machine-checked structure already present for the nontrivial shift operator;
-- 2. derived finite-profile Lorentz uniqueness and transported constraint closure;
-- 3. constructive Yang--Mills / OS / continuum targets which remain analytic inputs.
--
-- In particular, the shift operator and the current projection-defect quadratic
-- model are packaged together here, but are not identified without an explicit
-- comparison theorem.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperatorStackShift as ROS
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP

open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.ConeArrowIsotropyForcesProfileShiftInstance as CAFSI

open import DASHI.Physics.Constraints.Closure using (ClosureLaw)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem as CCFCPT

open import DASHI.Physics.YangMills.CompactLieYangMillsFrontier as YMF

------------------------------------------------------------------------
-- I. Actual shift operator -> projection-defect/parallelogram seam
------------------------------------------------------------------------

record ShiftOperatorDefectHierarchyEvidence (m k : Nat) : Setω where
  field
    canonicalizationNonexpansive :
      SCC.NonExpansive
        (FAM.ultrametricVec {n = m + k})
        (ROS.C {m} {k})

    refinementNonexpansive :
      SCC.NonExpansive
        (FAM.ultrametricVec {n = m + k})
        (ROS.R {m} {k})

    projectionNonexpansive :
      SCC.NonExpansive
        (FAM.ultrametricVec {n = m + k})
        (ROS.P {m} {k})

    projectionStrictOnFibers :
      FC.ContractiveOnFibers
        (FAM.ultrametricVec {n = m + k})
        (ROS.P {m} {k})

    projectionIdempotent :
      ∀ x → ROS.P {m} {k} (ROS.P {m} {k} x) ≡ ROS.P {m} {k} x

shiftOperatorDefectHierarchyEvidence :
  ∀ (m k : Nat) → ShiftOperatorDefectHierarchyEvidence m k
shiftOperatorDefectHierarchyEvidence m k =
  record
    { canonicalizationNonexpansive = ROS.nonexpC {m} {k}
    ; refinementNonexpansive = ROS.nonexpR {m} {k}
    ; projectionNonexpansive = ROS.nonexpP {m} {k}
    ; projectionStrictOnFibers = ROS.strictP-fiber {m} {k}
    ; projectionIdempotent = TCP.Pᵣ-idem m k
    }

-- This is the exact missing comparison theorem.  Its inhabitant must show that
-- the concrete shift projection/defect hierarchy induces the additive
-- projection-defect package used by the quadratic-emergence route.
record ShiftOperatorToQuadraticComparison (m k : Nat) : Setω where
  field
    operatorEvidence : ShiftOperatorDefectHierarchyEvidence m k
    inducedParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {m + k}) QES.ScalarFieldℤ

-- The target package is already independently inhabited for Q-hat-core.  This
-- constructor records the current cross-pollinated state without claiming that
-- PDzero is definitionally the same projection as the ternary shift operator.
shiftOperatorWithCurrentQuadraticModel :
  ∀ (m k : Nat) → ShiftOperatorToQuadraticComparison m k
shiftOperatorWithCurrentQuadraticModel m k =
  record
    { operatorEvidence = shiftOperatorDefectHierarchyEvidence m k
    ; inducedParallelogram = PDSP.projectionDefectParallelogramFromSplit
    }

------------------------------------------------------------------------
-- II. Explicit finite-profile Lorentz uniqueness
------------------------------------------------------------------------

record ExplicitLorentz31Hypotheses : Setω where
  field
    FiniteSpeedCompatible : Set
    finiteSpeedCompatible : FiniteSpeedCompatible
    AdmissibleSignature : OSD.Signature → Set
    sig31Admissible : AdmissibleSignature OSD.sig31
    admissibleHasMeasuredProfile :
      ∀ s → AdmissibleSignature s →
      CAFSI.shiftMeasuredProfile ≡ OSD.ProfileOf s

record ExplicitLorentz31Uniqueness : Setω where
  field
    hypotheses : ExplicitLorentz31Hypotheses
    selected : OSD.Signature
    selectedIs31 : selected ≡ OSD.sig31
    uniqueAmongAdmissible :
      ∀ s →
      ExplicitLorentz31Hypotheses.AdmissibleSignature hypotheses s →
      s ≡ OSD.sig31

explicitLorentz31Uniqueness :
  ExplicitLorentz31Hypotheses → ExplicitLorentz31Uniqueness
explicitLorentz31Uniqueness hypotheses =
  record
    { hypotheses = hypotheses
    ; selected = OSD.sig31
    ; selectedIs31 = OSD.SignatureFromMeasuredProfileUnique
        OSD.sig31
        (ExplicitLorentz31Hypotheses.admissibleHasMeasuredProfile
          hypotheses
          OSD.sig31
          (ExplicitLorentz31Hypotheses.sig31Admissible hypotheses))
    ; uniqueAmongAdmissible = λ s admissible →
        CAFSI.shiftSignatureForced31
          s
          (ExplicitLorentz31Hypotheses.admissibleHasMeasuredProfile
            hypotheses s admissible)
    }

------------------------------------------------------------------------
-- III. Forced geometry -> transported canonical constraint closure
------------------------------------------------------------------------

record ForcedGeometryConstraintClosure : Setω where
  field
    contractionQuadraticSignature :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    canonicalPath : CCFCPT.CanonicalPathWitness
    closureLaw : ClosureLaw CI.CS CI.L

canonicalForcedGeometryConstraintClosure :
  ForcedGeometryConstraintClosure
canonicalForcedGeometryConstraintClosure =
  record
    { contractionQuadraticSignature =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; canonicalPath = CCFCPT.canonicalPathWitness
    ; closureLaw = CCFCPT.canonicalPathInducedConstraintClosure
    }

------------------------------------------------------------------------
-- IV. Constructive Yang--Mills / OS / continuum analytic frontier
------------------------------------------------------------------------

-- A single exact bundle of the remaining analytic inhabitants.  There is no
-- canonical constructor in this module: supplying one would amount to proving
-- the corresponding constructive Yang--Mills and continuum statements.
record ConstructiveYangMillsContinuumObligations : Setω where
  field
    residualContraction :
      YMF.UniformResidualContractionTarget Set Set Set
    largeFieldStepV :
      YMF.LargeFieldStepVTarget Set Set
    allScaleRG :
      YMF.AllScaleRGTarget Set Set
    continuumOS :
      YMF.ContinuumOSTarget Set
    physicalMassGap :
      YMF.PhysicalMassGapTarget Set Set

record CrossPollinatedPhysicsAdvance : Setω where
  field
    shiftOperatorQuadraticComparison :
      ShiftOperatorToQuadraticComparison 4 4
    forcedGeometryConstraintClosure :
      ForcedGeometryConstraintClosure
    constructiveContinuumFrontier :
      ConstructiveYangMillsContinuumObligations → Setω

canonicalCrossPollinatedPhysicsAdvance : CrossPollinatedPhysicsAdvance
canonicalCrossPollinatedPhysicsAdvance =
  record
    { shiftOperatorQuadraticComparison =
        shiftOperatorWithCurrentQuadraticModel 4 4
    ; forcedGeometryConstraintClosure =
        canonicalForcedGeometryConstraintClosure
    ; constructiveContinuumFrontier = λ _ → ⊤
    }

-- Proof-level honesty remains inherited from the Yang--Mills frontier ledger.
continuumOSRemainsConjectural :
  YMF.claimLocallyPromotable YMF.continuumOSAxioms ≡ false
continuumOSRemainsConjectural = YMF.massGapDoesNotSelfPromote

physicalMassGapRemainsConjectural :
  YMF.claimLocallyPromotable YMF.positivePhysicalMassGap ≡ false
physicalMassGapRemainsConjectural = YMF.massGapDoesNotSelfPromote
