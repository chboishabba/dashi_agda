module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound74TopDownHoleCompilerExact where

------------------------------------------------------------------------
-- ROUND74: TOP-DOWN HOLE COMPILER, NOT A FRONTIER COUNT
--
-- The endpoint remains the literal five-role compiler.  Round73 identified
-- eight theorem-sized analytic jobs below it.  Round74 now descends each job
-- until either an existing source/repository theorem closes the branch or the
-- FIRST genuinely physical analytic leaf appears.
--
-- This file deliberately does not claim that "eight remain" is proof
-- architecture.  The architecture is the implication graph below.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Literal endpoint.
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact

-- Round73 diagnostic cutset.
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound73EightAnalyticCutsetExact

-- #1 selected background / signed G2.
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact

-- #2 literal one-loop coefficient.
import DASHI.Physics.YangMills.BalabanSU2OneLoopInfraredCoefficientFromLiteralScalarExact
import DASHI.Physics.YangMills.BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact

-- #3 source carrier weld.
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact

-- #4 unified strong extension.
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact

-- #5 backwards completion through a measure-defining coordinate.
import DASHI.Physics.YangMills.BalabanUnifiedCompletedStateProjectionExact
import DASHI.Physics.YangMills.BalabanUnifiedCharacteristicFunctionalCompletionExact as Characteristic

-- #6 group-native gap route.
import DASHI.Physics.YangMills.CompactSimpleBiInvariantRicciReserveExact
import DASHI.Physics.YangMills.CompactLieBiInvariantRicciNonnegativeExact
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as Heat
import DASHI.Physics.YangMills.CompactLieHeatDoobRicciReserveDebtExact as ReserveDebt
import DASHI.Physics.YangMills.CompactLieHeatDoobLogHessianNumeratorExact
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact

-- #7 local fields/OPE/stress.
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact

-- #8 nontriviality: cumulant route plus cheaper free-theory obstruction test.
import DASHI.Physics.YangMills.BalabanUnifiedContinuumEndpointMarginTransportExact
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free

------------------------------------------------------------------------
-- ACTUAL THEOREM-PRODUCING COMPOSITIONS DISCOVERED BY THE BACKWARDS PASS
------------------------------------------------------------------------

-- #5: once the augmented strong state supplies a characteristic functional with
-- closed finite laws and same-family moment identification, the continuum
-- probability measure is CONSTRUCTED from that same completed state.  No
-- independent measure subsequence remains.
round74CharacteristicCompletion = Characteristic.assembleUnifiedContinuumMeasure

-- #6: positive compact-simple Ricci reserve plus uniformly bounded cumulative
-- negative Hessian debt is sufficient for the group heat/Doob LSI.  The old
-- arbitrary-curvature-history producer is not needed.
round74RicciReserveDebtToLSI = ReserveDebt.ricciReserveDebtGivesLSI

-- #8 alternative: a massless one-particle sector contradicts any positive
-- spectral gap.  This becomes a nontriviality proof only after the two explicit
-- same-theory semantic bridges recorded in the free-Maxwell module are proved.
round74MasslessSectorNoGap = Free.masslessSectorContradictsPositiveGap

------------------------------------------------------------------------
-- FIRST PHYSICAL LEAVES FOR EACH ROUND73 JOB
--
-- #1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--    FIRST LEAF:
--      construct, for arbitrary QuantitativeCompactLiePackage G, the literal
--      selected-background/KKT/Green source map producing
--
--        R_i <= r_i Q (i=1..4),  g Q <= G_11,
--        r1+r2+r3+r4-g <= 55/18874368.
--    Everything after those five scalar inequalities is already exact signed
--    absorption.
--
-- #2 LiteralWilsonFPHaarOneLoopRGCoefficient
--    FIRST LEAVES:
--      (a) literal Wilson + FP + Haar Ward/transverse scalar reduction on the
--          source carrier;
--      (b) four canonical regular-remainder interval enclosures / atom
--          covariance.  The universal SU2 11/12 coefficient and 240->4 orbit
--          transport are already exact downstream.
--
-- #3 LiteralStateEntersPublishedBalabanRG
--    FIRST LEAF:
--      one same-object Section-2 dictionary extracting the actual repository
--      coordinates (coupling, small/large field, covariance, decay, spacing,
--      plus source E^(2)) from the literal effective density.  CMP119/CMP122
--      then own the baseline finite-cutoff nonlinear RG preservation.
--
-- #4 PhysicalUnifiedOneStepYMEstimate
--    FIRST LEAVES AFTER #3:
--      extend the SAME source flow by genuinely extra strong coordinates:
--      composite insertions, separation-weighted connected correlations, and
--      a common increment modulus; identify source E^(2)/Pi with the unified
--      derivative/Hessian coordinate.  Baseline small/large/localized RG
--      stability and differentiated exponential localization are source-owned.
--
-- #5 SameFamilyContinuumOSCompletion
--    BACKWARDS REDUCTION:
--      augment #4's same strong state with one characteristic-functional
--      coordinate.  Then the first remaining leaves are
--        (a) same-modulus characteristic convergence,
--        (b) nuclear continuity closed uniformly in the chosen topology,
--        (c) Schwinger projection = moment family of the same characteristic,
--        (d) standard OS reconstruction on this same limit.
--      Proving (a)-(d) makes #5 a theorem consequence of strengthened #4 and
--      yields a genuine future 8->7 reduction.
--
-- #6 SameDensityCompactLieHeatLangevinClustering
--    BACKWARDS REDUCTION:
--      standard compact-simple geometry gives Ric >= rho_G g with rho_G>0,
--      uniformly on finite products G^E.  Thus the curvature leaf is only
--
--        Hess V_t >= -eta(t) g,
--        integral_0^t eta <= M uniformly.
--
--      Equivalently, for u_t=H_t(exp(-V0)), prove the division-free numerator
--
--        (X u_t)^2 - u_t Hess u_t(X,X)
--          + eta(t) u_t^2 |X|^2 >= 0.
--
--      Then I <= exp(2M)/rho_G and the LSI follows.  The remaining propagation
--      leaf is the literal covariant derivative equation whose symmetric
--      influence is the SAME quasi-local Hessian; its bi-invariant ad/connection
--      energy term already cancels exactly.  Weighted propagation + temporal
--      relaxation gives spatial clustering; OS gap interpretation is downstream.
--
-- #7 SameFamilyCompositeOPEStressWardClosure
--    FIRST LEAVES:
--      (a) nonperturbative composite-field mixing/OPE remainder estimate in the
--          completed unified state, with explicit dyadic vanishing modulus;
--      (b) protected stress-tensor Ward theorem on the same state, including
--          H = integral T_00 for the SAME reconstructed Hamiltonian.
--
-- #8 FiniteScaleStrictFourthCumulantMargin
--    AUTHORITATIVE CURRENT LEAF:
--      one strict finite-scale connected fourth-cumulant buffer larger than the
--      common continuum tail.
--    CHEAPER ALTERNATIVE UNDER TEST:
--      positive physical gap already excludes a free Gaussian theory IF
--        free/Gaussian YM -> same-theory massless Maxwell sector
--      and
--        not free/Gaussian -> literal Clay nontriviality.
--      The spectral zero-gap implication itself is already exact.  Until these
--      two bridges are proved, do not delete the cumulant route.
------------------------------------------------------------------------

-- The point of this root is that future work attacks these first leaves directly
-- and reruns the compiler.  A numerical count may fall as implications are
-- proved, but it is not the proof architecture.
round74TopDownHoleCompilerLevel : ProofLevel
round74TopDownHoleCompilerLevel = machineChecked
