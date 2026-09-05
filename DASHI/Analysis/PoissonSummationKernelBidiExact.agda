module DASHI.Analysis.PoissonSummationKernelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC POISSON-SUMMATION KERNEL
--
-- This is intentionally theorem-shape infrastructure, not a theorem imported
-- from the Riemann lane.  An application must supply its own function,
-- transform, lattice, convergence/regularity, and equality receipt.
------------------------------------------------------------------------

record PoissonSummationProblem : Set₁ where
  field
    Function : Set
    Transform : Set
    LatticePoint : Set
    DualPoint : Set
    Value : Set

    function : Function
    transform : Transform

    primalTerm : Function → LatticePoint → Value
    dualTerm : Transform → DualPoint → Value

    primalSum dualSum : Value

    analyticHypotheses : Set
    latticeDualityHypotheses : Set
    summationConvergenceHypotheses : Set

    reading : String

open PoissonSummationProblem public

record PoissonSummationReceipt (P : PoissonSummationProblem) : Set₁ where
  field
    hypothesesClosed :
      analyticHypotheses P ×
      (latticeDualityHypotheses P × summationConvergenceHypotheses P)

    poissonEquality : primalSum P ≡ dualSum P
    receiptReading : String

open PoissonSummationReceipt public

------------------------------------------------------------------------
-- Reverse direction: a prospective consumer can expose the exact hypotheses
-- required to instantiate the generic kernel on its own object.
------------------------------------------------------------------------

record PoissonConsumerObligations (P : PoissonSummationProblem) : Set₁ where
  field
    functionTransformSameObject : Set
    latticePairSameObject : Set
    analyticDomainClosed : Set
    convergenceClosed : Set

open PoissonConsumerObligations public

------------------------------------------------------------------------
-- Sideways-import firewall.
------------------------------------------------------------------------

data ForeignPoissonInstancePermission : Set where

foreignPoissonInstanceCannotAutoDischarge :
  {P : PoissonSummationProblem} →
  PoissonSummationReceipt P →
  ForeignPoissonInstancePermission → ⊥
foreignPoissonInstanceCannotAutoDischarge receipt ()
