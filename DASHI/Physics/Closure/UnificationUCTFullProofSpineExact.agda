{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.UnificationUCTFullProofSpineExact where

------------------------------------------------------------------------
-- PAPER 8 / UCT.1--UCT.4 TYPED PROOF SPINE
--
-- The live Paper-8 mathematical wall is:
--
--   UCT.1 exact residual PDE
--     -> UCT.2 elliptic/parabolic operator class
--     -> UCT.3 matched unique-continuation/Carleman theorem
--     -> UCT.4 gluing cross-term nullity.
--
-- Downstream modulo-null, four-point, parallelogram and JvN consumers are not
-- primitive inputs here.  This file ties the analytic spine to the repository's
-- exact `actualU1aCrossTerm` carrier and compiles a genuine UCT.4 witness into
-- the pre-existing theorem target.  It does not inhabit UCT.1--UCT.4 itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary as U1a
import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary as Boundary

record UCTAnalyticPackage
    (V : U1a.AdmissibleDefectQuotientVBoundary)
    (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    -V_ :
      U1a.DefectQuotientV V → U1a.DefectQuotientV V

    nullClass :
      U1a.DefectQuotientV V → Set

    -- UCT.1: exact residual PDE satisfied by a cross-term candidate.
    ResidualPDE :
      U1a.DefectQuotientV V → Set

    uct1ResidualPDE :
      (s1 s2 : U1a.DefectQuotientV V) →
      ResidualPDE
        (Boundary.actualU1aCrossTerm V G-boundary -V_ s1 s2)

    -- UCT.2: exact operator regime for the UCT.1 residual equation.
    OperatorClass :
      U1a.DefectQuotientV V → Set

    uct2OperatorClass :
      (x : U1a.DefectQuotientV V) →
      ResidualPDE x →
      OperatorClass x

    -- UCT.3: theorem applicability matched to that operator class.
    UniqueContinuationAdmissible :
      U1a.DefectQuotientV V → Set

    uct3UniqueContinuationIntake :
      (x : U1a.DefectQuotientV V) →
      OperatorClass x →
      UniqueContinuationAdmissible x

    -- UCT.4: the actual mathematical implication consumed by U-1a.
    uct4CrossTermNullity :
      (x : U1a.DefectQuotientV V) →
      UniqueContinuationAdmissible x →
      nullClass x

open UCTAnalyticPackage public

uct4CrossTermNullityTheorem :
  ∀ {V G-boundary} →
  (package : UCTAnalyticPackage V G-boundary) →
  (s1 s2 : U1a.DefectQuotientV V) →
  nullClass package
    (Boundary.actualU1aCrossTerm
      V G-boundary (-V_ package) s1 s2)
uct4CrossTermNullityTheorem {V} {G-boundary} package s1 s2 =
  uct4CrossTermNullity package crossTerm
    (uct3UniqueContinuationIntake package crossTerm
      (uct2OperatorClass package crossTerm
        (uct1ResidualPDE package s1 s2)))
  where
    crossTerm : U1a.DefectQuotientV V
    crossTerm =
      Boundary.actualU1aCrossTerm
        V G-boundary (-V_ package) s1 s2

asU1aCrossTermNullityTheoremTarget :
  ∀ {V G-boundary} →
  (package : UCTAnalyticPackage V G-boundary) →
  Boundary.U1aCrossTermNullityTheoremTarget V G-boundary
asU1aCrossTermNullityTheoremTarget package = record
  { Boundary.U1aCrossTermNullityTheoremTarget.-V_ = -V_ package
  ; Boundary.U1aCrossTermNullityTheoremTarget.nullClass = nullClass package
  ; Boundary.U1aCrossTermNullityTheoremTarget.theoremTarget =
      uct4CrossTermNullityTheorem package
  ; Boundary.U1aCrossTermNullityTheoremTarget.theoremTargetText =
      "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"
  ; Boundary.U1aCrossTermNullityTheoremTarget.theoremTargetTextIsCanonical = refl
  }

uctAnalyticSpineCompilerLevel : ProofLevel
uctAnalyticSpineCompilerLevel = machineChecked

uct1ResidualPDEPhysicalLevel : ProofLevel
uct1ResidualPDEPhysicalLevel = conditional

uct2OperatorClassPhysicalLevel : ProofLevel
uct2OperatorClassPhysicalLevel = conditional

uct3UniqueContinuationPhysicalLevel : ProofLevel
uct3UniqueContinuationPhysicalLevel = conditional

uct4CrossTermNullityPhysicalLevel : ProofLevel
uct4CrossTermNullityPhysicalLevel = conditional
