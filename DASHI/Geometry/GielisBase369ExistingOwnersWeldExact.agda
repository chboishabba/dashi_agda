module DASHI.Geometry.GielisBase369ExistingOwnersWeldExact where

-- A proof-preserving reuse seam. Do not re-prove Shannon, the dihedral
-- relation, C3 orientation, MDL cost, or continuous R3 cross product.
-- The finite Nyquist witness has a real information-loss example, while the
-- sampling / information-theoretic promotion gates remain separate.
-- Not a claim that all of these carriers denote the same physical device.

open import DASHI.Core.Prelude
open import Data.Integer using (+_)

import DASHI.Geometry.GielisBase369FiniteExact as Gielis
import DASHI.Geometry.GielisBase369NyquistPhase36Exact as Nyquist
import DASHI.Foundations.Base369CirclePhase as Phase
import DASHI.Foundations.Base369EngineeringMDL as MDL
import DASHI.Cognition.PNF.SemanticSamplingLookupGeometry as Sampling
import DASHI.Biology.Physical.DNAHelixDihedralExact as DNA
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Physics.Foundations.ContinuousSO3Torque369BridgeExact as Continuous
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge
import DASHI.Cognition.AnalyticLogPolarSpiralCompilerExact as LogPolar
import DASHI.Cognition.CorticalLogPolarProjectionGeometry as Visual

-- The existing physical/biological dihedral owner is invoked verbatim.
existingDNADihedralConjugation :
  (p : DNA.Phase4) →
  DNA.reflect (DNA.rotate (DNA.reflect p)) ≡ DNA.rotateInv p
existingDNADihedralConjugation = DNA.dihedralConjugation

-- New finite Gielis symmetry is distinct from DNA, but has the same
-- relation as a group action; do not identify the carriers by cardinality.
gielisSixfoldDihedralConjugation :
  (p : Phase.Phase18) →
  Gielis.reflect18 (Gielis.rotate6 p)
  ≡ Gielis.rotate6Inverse (Gielis.reflect18 p)
gielisSixfoldDihedralConjugation = Gielis.reflectRotate6

-- The original torque owner has an exact finite orientation classifier.
-- This result is not an equality between that trit and physical Nm torque.
existingTorqueInputReversal :
  (v : Torque.BracketVoxel) →
  Torque.torqueOrientation (Torque.swapTorqueInputs v)
  ≡ Trit.negate (Torque.torqueOrientation v)
existingTorqueInputReversal = Torque.swapTorqueInputsNegatesOrientation

-- The R3 Hodge/cross interface belongs to the existing torque lane.
existingCrossProductIdentification :
  ∀ x y →
  Hodge.hodgeStar3 (Hodge.wedge3 x y)
  ≡ Hodge.cross3 x y
existingCrossProductIdentification = Hodge.hodgeWedgeEqualsCross

-- Existing canonical MDL cost, re-used as an explicit cost owner.
existing369MDLControlCost :
  MDL.controlProgramLength
    (MDL.costExpr369 MDL.syntacticCostModel369 Phase.fortyFiveExpr)
  ≡ 5
existing369MDLControlCost = MDL.fortyFive-control-program-length

-- Existing Nyquist analogy explicitly does NOT import a classical
-- Shannon sampling theorem into semantic resolution spaces.
semanticSamplingIsNotClassicalNyquist :
  Sampling.SemanticSamplingLookupBoundary.queryCommutationIsClassicalNyquistTheorem
    Sampling.canonicalSemanticSamplingLookupBoundary
  ≡ false
semanticSamplingIsNotClassicalNyquist =
  Sampling.SemanticSamplingLookupBoundary.queryCommutationIsClassicalNyquistTheoremIsFalse
    Sampling.canonicalSemanticSamplingLookupBoundary

-- Reuse the existing log-polar/spiral feature projection, not an
-- unaudited new logarithmic spiral law.
existingSpiralFeature :
  Visual.FeatureProjectsAs
    LogPolar.analyticFeature
    LogPolar.analyticForm
existingSpiralFeature = LogPolar.analyticFeatureProjectsAsSpiral

-- Native finite orientation separation is the *new* part of this seam.
gielisOrientationResolvesAfterRefinement :
  Nyquist.sinNine Nyquist.p36-1
  ≡ + 1
gielisOrientationResolvesAfterRefinement = Nyquist.fineNineAtOne

-- Critical open bridges:
-- 1. actual ordinary-real Gielis function <-> tabulated trigonometric modes
-- 2. bandlimited Shannon reconstruction <-> selected 18/36 sampling maps
-- 3. meaningful Kolmogorov/MDL code and distortion model
-- 4. measured/calibrated optical impulse <-> R3 torque and lever arm
-- 5. original Kozyrev reflector geometry <-> selected new ray scene
