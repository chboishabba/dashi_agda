module DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Continuum Einstein--matter solution boundary.
--
-- A continuum solution is more than a tensor table: it needs a manifold,
-- metric, matter fields, field equations, constraints, regularity, and a domain
-- on which the equations hold.  This module packages those obligations and
-- proves the conservation consequence once Einstein equality and contracted
-- Bianchi are supplied.

record ContinuumEinsteinMatterSystem : Set₁ where
  constructor mkContinuumEinsteinMatterSystem
  field
    Point : Set
    Index : Set
    Scalar : Set
    zero : Scalar
    MetricField : Set
    MatterField : Set
    EinsteinTensor : MetricField → Point → Index → Index → Scalar
    StressTensor : MatterField → MetricField → Point → Index → Index → Scalar
    DivergenceEinstein : MetricField → Point → Index → Scalar
    DivergenceStress : MatterField → MetricField → Point → Index → Scalar
    systemLabel : String

open ContinuumEinsteinMatterSystem public

record ContinuumSolutionData (S : ContinuumEinsteinMatterSystem) : Set where
  constructor mkContinuumSolutionData
  field
    metric : MetricField S
    matter : MatterField S
    smoothOrControlledRegularity : Bool
    LorentzianSignature : Bool
    globalOrDeclaredDomain : Bool
    initialOrBoundaryDataSupplied : Bool
    EinsteinEquation :
      (p : Point S) → (a b : Index S) →
      EinsteinTensor S metric p a b ≡ StressTensor S matter metric p a b
    contractedBianchi :
      (p : Point S) → (b : Index S) →
      DivergenceEinstein S metric p b ≡ zero S
    divergenceRespectsEinsteinEquality :
      (p : Point S) → (b : Index S) →
      DivergenceStress S matter metric p b ≡ DivergenceEinstein S metric p b
    solutionScope : String

open ContinuumSolutionData public

matterConservationFromEinsteinAndBianchi :
  (S : ContinuumEinsteinMatterSystem) →
  (solution : ContinuumSolutionData S) →
  (p : Point S) → (b : Index S) →
  DivergenceStress S (matter solution) (metric solution) p b ≡ zero S
matterConservationFromEinsteinAndBianchi S solution p b =
  Agda.Builtin.Equality.trans
    (divergenceRespectsEinsteinEquality solution p b)
    (contractedBianchi solution p b)

record ContinuumSolutionPromotionBoundary : Set where
  constructor mkContinuumSolutionPromotionBoundary
  field
    solutionSchemaImplemented : Bool
    finiteWarpedSolutionAvailable : Bool
    smoothContinuumExistenceProved : Bool
    globalWellPosednessProved : Bool
    physicallyDerivedMatterModel : Bool
    observationallyMatchedSolution : Bool
    boundaryStatement : String

open ContinuumSolutionPromotionBoundary public

canonicalContinuumSolutionPromotionBoundary : ContinuumSolutionPromotionBoundary
canonicalContinuumSolutionPromotionBoundary =
  mkContinuumSolutionPromotionBoundary
    true true false false false false
    "the continuum solution contract and conservation eliminator are implemented; no smooth global physical Einstein-matter solution is claimed"

canonicalContinuumSolutionNotYetProved :
  smoothContinuumExistenceProved canonicalContinuumSolutionPromotionBoundary ≡ false
canonicalContinuumSolutionNotYetProved = refl
