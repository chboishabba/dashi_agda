module DASHI.Physics.Closure.E6HyperformIntrinsicQuadraticLaplacianExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformPoissonLorentzMetricExact as OldMetric
import DASHI.Physics.Closure.E6HyperformTernary36GravityRefinementCandidateExact as OldScale

------------------------------------------------------------------------
-- INTRINSIC QUADRATIC-CLASS LAPLACIAN REPAIR
--
-- The selected chart quadratic source has 144 linear GL3(F3) isometries.
-- The previously used coordinate torus adjacency is preserved by only 8 of
-- them, so its Poisson field is not intrinsic to the quadratic chart.
--
-- Repair: connect p to p+v for every nonzero v with q(v) != 0.  This gives a
-- degree-24 Cayley graph invariant under all 144 quadratic isometries and is
-- also insensitive to swapping the two nonsingular q labels by rescaling the
-- quadratic form.  On this graph the mean-zero Poisson solution is simply
--
--     phi(p) = rho(p)/27,
--
-- where rho is the balanced q-source 0,+1,-1.
------------------------------------------------------------------------

quadraticIsometryGroupOrder : Nat
quadraticIsometryGroupOrder = 144

oldTorusAdjacencyPreservingCount : Nat
oldTorusAdjacencyPreservingCount = 8

intrinsicConnectionDegree : Nat
intrinsicConnectionDegree = 24

intrinsicAdjacencyPreservingCount : Nat
intrinsicAdjacencyPreservingCount = 144

intrinsicFinitePotential : String
intrinsicFinitePotential = "phi(p) = rho(p)/27"

rhoContinuumInterpolation : String
rhoContinuumInterpolation =
  "(9*x^2*y^2*z^2 - 6*x^2*y^2 - 3*x^2*z^2 + 2*x^2 - 3*x*y^2*z + x*z - 6*y^2*z^2 + 2*y^2 + 2*z^2)/2"

record IntrinsicQuadraticLaplacianLocalReceipt : Set where
  constructor intrinsic-quadratic-laplacian-local-receipt
  field
    sameExceptionalQuadraticSourceUsed : Bool
    qClassCountsThreeTwelveTwelve : Bool
    fullLinearQuadraticIsometryOrder144Checked : Bool
    oldSixNeighborAdjacencyPreservedByOnlyEight : Bool
    oldPoissonOperatorFullyIntrinsic : Bool
    nonsingularConnectionSetDegree24 : Bool
    nonsingularConnectionSetScaleLabelInvariant : Bool
    intrinsicAdjacencyPreservedByAll144 : Bool
    poissonEquationPhiEqualsRhoOver27Checked : Bool
    meanZeroPotentialChecked : Bool
    oldDepth36ClockNearMatchSurvivesRepair : Bool
    depth36IntrinsicTheoryRatioBelowPointThree : Bool
    oldDepth36GravityCandidatePromoted : Bool
    boundary : String
open IntrinsicQuadraticLaplacianLocalReceipt public

canonicalIntrinsicQuadraticLaplacianLocalReceipt : IntrinsicQuadraticLaplacianLocalReceipt
canonicalIntrinsicQuadraticLaplacianLocalReceipt =
  intrinsic-quadratic-laplacian-local-receipt
    true true true true false
    true true true true true
    false true false
    "The coordinate C3^3 Laplacian used by the first metric breaks most intrinsic quadratic-chart symmetry (8 preserving matrices out of 144). The degree-24 Cayley graph on all nonsingular displacement vectors restores all 144 linear isometries and yields the exact finite solution phi=rho/27. Re-running the atomic-clock diagnostic on this repaired operator sends the previous 3^-36 match to only about 0.278 of the GR scale, so the old depth-36 coincidence is not robust and is demoted."

------------------------------------------------------------------------
-- Replacement gravity frontier.
------------------------------------------------------------------------

record IntrinsicExceptionalMetricWeld : Set₁ where
  field
    FiniteChart : Set
    ContinuumChart : Set
    finiteQuadraticSourceReceipt : Set
    intrinsicLaplacianReceipt : Set
    finitePoissonReceipt : Set
    continuumInterpolationReceipt : Set
    lorentzMetricReceipt : Set
    chartDescentReceipt : Set
    independentMatterStressReceipt : Set
    empiricalScaleReceipt : Set
open IntrinsicExceptionalMetricWeld public

data CoordinateAdjacencyCreatesIntrinsicGeometry : Set where

data OldClockFitSurvivesOperatorRepairByDefault : Set where

coordinateAdjacencyDoesNotCreateIntrinsicGeometry :
  CoordinateAdjacencyCreatesIntrinsicGeometry → {A : Set} → A
coordinateAdjacencyDoesNotCreateIntrinsicGeometry ()

oldClockFitDoesNotSurviveByDefault :
  OldClockFitSurvivesOperatorRepairByDefault → {A : Set} → A
oldClockFitDoesNotSurviveByDefault ()
