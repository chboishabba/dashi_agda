module DASHI.Physics.YangMills.BalabanReducedFaddeevPopovPhysicalFourthJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- DASHI CONTRIBUTION
--
-- Assemble the four algebraic background coefficients of the SAME literal
-- physical Faddeev--Popov operator M_A = D_A G_A.  For a rational tangent
-- bond field X, exp(gX) is Bishop-real away from g=0, while every Taylor
-- coefficient at zero is rational.  The linkwise adjoint coefficients are
-- threaded through forward G_A and backward D_A, postcomposed with the exact
-- reduced M0^{-1}, converted to the explicit 765-dimensional matrices, and
-- immediately fed into the already-proved fourth-order trace-log algebra.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact as FlatInverse
import DASHI.Physics.YangMills.BalabanReducedGhostExplicitTraceCarrierExact as Basis
import DASHI.Physics.YangMills.BalabanReducedGhostOperatorMatrixExact as MatrixCarrier
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovTraceLogJetExact as TraceJet
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovMatrixTraceLogJetExact as TraceMatrix
import DASHI.Physics.YangMills.BalabanReducedGhostAdjointFourthJetExact as Jet

zeroJet : Jet.QuaternionJet4
zeroJet = Jet.jet4 Jet.zeroQ Jet.zeroQ Jet.zeroQ Jet.zeroQ Jet.zeroQ

addJet : Jet.QuaternionJet4 → Jet.QuaternionJet4 → Jet.QuaternionJet4
addJet left right = Jet.jet4
  (Jet.addQ (Jet.c0 left) (Jet.c0 right))
  (Jet.addQ (Jet.c1 left) (Jet.c1 right))
  (Jet.addQ (Jet.c2 left) (Jet.c2 right))
  (Jet.addQ (Jet.c3 left) (Jet.c3 right))
  (Jet.addQ (Jet.c4 left) (Jet.c4 right))

negJet : Jet.QuaternionJet4 → Jet.QuaternionJet4
negJet value = Jet.jet4
  (Jet.negQ (Jet.c0 value))
  (Jet.negQ (Jet.c1 value))
  (Jet.negQ (Jet.c2 value))
  (Jet.negQ (Jet.c3 value))
  (Jet.negQ (Jet.c4 value))

subJet : Jet.QuaternionJet4 → Jet.QuaternionJet4 → Jet.QuaternionJet4
subJet left right = addJet left (negJet right)

sumJet : List Periodic.Axis4 → (Periodic.Axis4 → Jet.QuaternionJet4) → Jet.QuaternionJet4
sumJet [] term = zeroJet
sumJet (axis ∷ axes) term = addJet (term axis) (sumJet axes term)

adjointJetOnJet : Q.RationalQuaternion → Jet.QuaternionJet4 → Jet.QuaternionJet4
adjointJetOnJet generator valueJet =
  Jet.mulJet
    (Jet.mulJet (Jet.expJet4 generator) valueJet)
    (Jet.inverseExpJet4 generator)

backgroundGeneratorQuaternion :
  Coordinates.PhysicalSU2BondField4 → Periodic.Axis4 → Periodic.Site4 →
  Q.RationalQuaternion
backgroundGeneratorQuaternion generator axis site =
  Gauge.insertionQuaternion generator axis site

forwardParameterAdjointJet :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Jet.QuaternionJet4
forwardParameterAdjointJet generator parameter axis site =
  Jet.adjointJet4
    (backgroundGeneratorQuaternion generator axis site)
    (FP.parameterQuaternion parameter (Periodic.shiftForward axis site))

backgroundGaugeOrbitJet :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Jet.QuaternionJet4
backgroundGaugeOrbitJet generator parameter axis site =
  subJet
    (Jet.constantJet (FP.parameterQuaternion parameter site))
    (forwardParameterAdjointJet generator parameter axis site)

backwardOrbitAdjointJet :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Jet.QuaternionJet4
backwardOrbitAdjointJet generator parameter axis site =
  let
    previous = Periodic.shiftBackward axis site
    inverseGenerator = Jet.negQ (backgroundGeneratorQuaternion generator axis previous)
  in
  adjointJetOnJet inverseGenerator
    (backgroundGaugeOrbitJet generator parameter axis previous)

faddeevPopovAxisJet :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Jet.QuaternionJet4
faddeevPopovAxisJet generator parameter axis site =
  subJet
    (backgroundGaugeOrbitJet generator parameter axis site)
    (backwardOrbitAdjointJet generator parameter axis site)

faddeevPopovQuaternionJet :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Periodic.Site4 → Jet.QuaternionJet4
faddeevPopovQuaternionJet generator parameter site =
  sumJet Gauge.axes4 (λ axis → faddeevPopovAxisJet generator parameter axis site)

coefficient1 coefficient2 coefficient3 coefficient4 :
  Coordinates.PhysicalSU2BondField4 → FP.SiteGaugeParameter4 →
  Gauge.GaugeCoordinate4 → ℚ
coefficient1 generator parameter (pair coordinate site) =
  Gauge.quaternionCoordinate coordinate
    (Jet.c1 (faddeevPopovQuaternionJet generator parameter site))
coefficient2 generator parameter (pair coordinate site) =
  Gauge.quaternionCoordinate coordinate
    (Jet.c2 (faddeevPopovQuaternionJet generator parameter site))
coefficient3 generator parameter (pair coordinate site) =
  Gauge.quaternionCoordinate coordinate
    (Jet.c3 (faddeevPopovQuaternionJet generator parameter site))
coefficient4 generator parameter (pair coordinate site) =
  Gauge.quaternionCoordinate coordinate
    (Jet.c4 (faddeevPopovQuaternionJet generator parameter site))

reducedCoefficient1 reducedCoefficient2 reducedCoefficient3 reducedCoefficient4 :
  Coordinates.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 →
  Basis.GhostLinearMap
reducedCoefficient1 generator anchor source =
  coefficient1 generator (FlatInverse.reducedFlatGreenInverse source anchor)
reducedCoefficient2 generator anchor source =
  coefficient2 generator (FlatInverse.reducedFlatGreenInverse source anchor)
reducedCoefficient3 generator anchor source =
  coefficient3 generator (FlatInverse.reducedFlatGreenInverse source anchor)
reducedCoefficient4 generator anchor source =
  coefficient4 generator (FlatInverse.reducedFlatGreenInverse source anchor)

physicalGhostX1 physicalGhostX2 physicalGhostX3 physicalGhostX4 :
  Coordinates.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 →
  Matrix.Matrix Gauge.GaugeCoordinate4
physicalGhostX1 generator anchor =
  MatrixCarrier.reducedGhostOperatorMatrix anchor
    (reducedCoefficient1 generator anchor)
physicalGhostX2 generator anchor =
  MatrixCarrier.reducedGhostOperatorMatrix anchor
    (reducedCoefficient2 generator anchor)
physicalGhostX3 generator anchor =
  MatrixCarrier.reducedGhostOperatorMatrix anchor
    (reducedCoefficient3 generator anchor)
physicalGhostX4 generator anchor =
  MatrixCarrier.reducedGhostOperatorMatrix anchor
    (reducedCoefficient4 generator anchor)

physicalReducedGhostMatrices4 :
  Coordinates.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 →
  TraceMatrix.FiniteGhostPerturbationMatrices4 Gauge.GaugeCoordinate4
physicalReducedGhostMatrices4 generator anchor = record
  { TraceMatrix.FiniteGhostPerturbationMatrices4.indices = Gauge.flatGaugeCoordinates
  ; TraceMatrix.FiniteGhostPerturbationMatrices4.X1 = physicalGhostX1 generator anchor
  ; TraceMatrix.FiniteGhostPerturbationMatrices4.X2 = physicalGhostX2 generator anchor
  ; TraceMatrix.FiniteGhostPerturbationMatrices4.X3 = physicalGhostX3 generator anchor
  ; TraceMatrix.FiniteGhostPerturbationMatrices4.X4 = physicalGhostX4 generator anchor
  }

physicalGhostTraceLogJet :
  Coordinates.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 →
  TraceJet.ReducedGhostTraceLogJet4
physicalGhostTraceLogJet generator anchor =
  TraceMatrix.matrixTraceLogJet4 (physicalReducedGhostMatrices4 generator anchor)

physicalFaddeevPopovFourthJetConstructionLevel : ProofLevel
physicalFaddeevPopovFourthJetConstructionLevel = machineChecked

physicalReducedGhostFourMatricesConstructionLevel : ProofLevel
physicalReducedGhostFourMatricesConstructionLevel = machineChecked

physicalReducedGhostTraceLogCoefficientsLevel : ProofLevel
physicalReducedGhostTraceLogCoefficientsLevel = machineChecked

-- The coefficient matrices and their fourth-order trace-log polynomial are now
-- source-native.  What remains is the analytic theorem that the Bishop
-- background path has these coefficients with a uniform O(g^5) remainder;
-- the determinant theorem then identifies the finite trace-log with log det on
-- the selected weak-coupling ball.
physicalReducedGhostBishopFifthOrderRemainderLevel : ProofLevel
physicalReducedGhostBishopFifthOrderRemainderLevel = conditional
