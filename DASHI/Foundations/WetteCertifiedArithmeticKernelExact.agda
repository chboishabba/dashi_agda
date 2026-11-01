module DASHI.Foundations.WetteCertifiedArithmeticKernelExact where

------------------------------------------------------------------------
-- COMPOSED CERTIFIED ARITHMETIC KERNEL
--
-- This is the first end-to-end repo-native Wette reconstruction composition:
--
--   ScalarTransportStep
--     -> CertifiedArithmeticTransitionFamily
--     -> WetteMachineSpec
--     -> WetteDeductionSimulation
--     -> RepresentationKernelCompatibility.
--
-- Every arrow is supplied by an existing owner or a thin adapter from this
-- tranche. The only deliberately weak point is the identity syntax witness:
-- it is an executable regression carrier, not Wette's recovered historical
-- grammar.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.GodelLattice using (FactorVec)

import DASHI.Foundations.WetteArithmeticTransitionBridgeExact as A
import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteRepresentationKernelBridgeExact as B
import DASHI.Physics.Closure.RepresentationKernelCompatibility as R

certifiedArithmeticCompatibility :
  (family : A.CertifiedArithmeticTransitionFamily) →
  (g : A.Generator family) →
  R.RepresentationKernelCompatibility
certifiedArithmeticCompatibility family g =
  B.fixedGeneratorCompatibility (A.arithmeticIdentitySimulation family) g

certifiedArithmeticTrajectoryCommutes :
  (family : A.CertifiedArithmeticTransitionFamily) →
  (g : A.Generator family) →
  (state : FactorVec) →
  ∀ n →
  R.iterate (A.arithmeticStep family g) n state
  ≡
  R.iterate
    (W.step (A.trivialArithmeticMachine family) g)
    n
    state
certifiedArithmeticTrajectoryCommutes family g state =
  B.canonicalTrajectoryCommutes
    (A.arithmeticIdentitySimulation family)
    g
    {term = state}
    refl

certifiedArithmeticFixedPointProjects :
  (family : A.CertifiedArithmeticTransitionFamily) →
  (g : A.Generator family) →
  {state : FactorVec} →
  R.FixedPoint (A.arithmeticStep family g) state →
  R.FixedPoint (W.step (A.trivialArithmeticMachine family) g) state
certifiedArithmeticFixedPointProjects family g =
  B.canonicalProjectedFixedPoint
    (A.arithmeticIdentitySimulation family)
    g
    refl

------------------------------------------------------------------------
-- The composed theorem remains representation/dynamics infrastructure only.
-- It supplies no historical Wette rule, soundness theorem, consistency proof,
-- or contradiction in ordinary arithmetic.
------------------------------------------------------------------------
