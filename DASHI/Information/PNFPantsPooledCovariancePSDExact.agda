module DASHI.Information.PNFPantsPooledCovariancePSDExact where

-- A finite PSD gluing theorem for a source-verified three-branch
-- quadratic decomposition with an explicit between-branch correction.
--
-- The existing combinatorial pants carrier provides an independent
-- channel/capacity/wave interface, NOT the covariance identity.
-- The observed quadratic must be proven equal to its three source
-- branch quadratics plus a nonnegative rank-one seam correction.
--
-- This is the common algebraic interface for grouped PNF activation
-- windows and grouped economic returns; it does not prove either
-- selected dataset obeys the decomposition without source receipts.

open import Agda.Builtin.Equality using (_≡_)
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as ExistingPSD
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

record ThreeBranchPooledQuadratic
  (K : Ring.ExactOrderedCommutativeRing)
  (O : ExistingPSD.FiniteGramOrderAuthority K) : Set₁ where
  private
    S = Ring.orderedScalar K
  field
    Vector : Set
    pantsBranching : Pants.OneToNBranching
    capacityReceipt : Pants.CapacityConservative pantsBranching
    waveReceipt : Pants.WaveConservative pantsBranching

    leftQuadratic : Vector → Scalar.Scalar S
    middleQuadratic : Vector → Scalar.Scalar S
    rightQuadratic : Vector → Scalar.Scalar S

    leftPSD :
      (v : Vector) → Scalar._≤_ S (Scalar.zero S) (leftQuadratic v)
    middlePSD :
      (v : Vector) → Scalar._≤_ S (Scalar.zero S) (middleQuadratic v)
    rightPSD :
      (v : Vector) → Scalar._≤_ S (Scalar.zero S) (rightQuadratic v)

    betweenProjection : Vector → Scalar.Scalar S
    betweenWeight : Scalar.Scalar S
    betweenWeightNonnegative :
      Scalar._≤_ S (Scalar.zero S) betweenWeight

    observedQuadratic : Vector → Scalar.Scalar S
    pooledQuadraticIdentity :
      (v : Vector) →
      observedQuadratic v ≡
        Scalar._+_ S
          (Scalar._+_ S
            (Scalar._+_ S
              (leftQuadratic v) (middleQuadratic v))
            (rightQuadratic v))
          (Scalar._*_ S betweenWeight
            (Ring.square S (betweenProjection v)))

open ThreeBranchPooledQuadratic public

-- A literal proof of the selected pooled quadratic's positivity.
-- The between-branch term remains a separate receipt: pants topology,
-- matching charts, and three individually PSD 2x2 marginals do NOT
-- imply the operator equality used here.
pooledPantsCovariancePSD :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : ExistingPSD.FiniteGramOrderAuthority K) →
  (P : ThreeBranchPooledQuadratic K O) →
  (v : ThreeBranchPooledQuadratic.Vector P) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (observedQuadratic P v)
pooledPantsCovariancePSD K O P v
  rewrite pooledQuadraticIdentity P v =
  ExistingPSD.addNonnegative O
    (ExistingPSD.addNonnegative O
      (ExistingPSD.addNonnegative O
        (leftPSD P v)
        (middlePSD P v))
      (rightPSD P v))
    (Scalar.multiplicationPreservesNonnegative (Ring.orderedScalar K)
      (betweenWeightNonnegative P)
      (ExistingPSD.squareNonnegative O
        (betweenProjection P v)))

-- The existing 1→3 pants witness is a legitimate three-branch
-- *combinatorial* interface, with separately proved conservations.
canonicalPantsThreeWayCapacityConservation :
  Pants.CapacityConservative Pants.composedOneToThree
canonicalPantsThreeWayCapacityConservation =
  Pants.composedCapacityConservative

canonicalPantsThreeWayWaveConservation :
  Pants.WaveConservative Pants.composedOneToThree
canonicalPantsThreeWayWaveConservation =
  Pants.composedWaveConservative
