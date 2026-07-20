module DASHI.Physics.YangMills.SUNMatrixGeometry where

------------------------------------------------------------------------
-- Quantitative invariant metric and local chart for the matrix SU(N) carrier.
-- The finite-dimensional analytic facts are standard imported; record assembly
-- into the generic compact-Lie geometry used by the Balaban lane is checked.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieGroupGeometry
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SUNInvariantMetricAuthority
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    traceInner : 𝔤 → 𝔤 → Scalar
    traceNorm : 𝔤 → Scalar
    biInvariantDistance : G → G → Scalar

    traceInnerSymmetric : ∀ X Y → traceInner X Y ≡ traceInner Y X
    traceNormNonnegative : ∀ X → _≤S_ S (zeroS S) (traceNorm X)
    adjointTraceIsometry : ∀ group X → traceNorm (Ad K group X) ≡ traceNorm X
    distanceLeftInvariant : ∀ x y z →
      biInvariantDistance (multiply (group K) x y) (multiply (group K) x z) ≡
      biInvariantDistance y z
    distanceRightInvariant : ∀ x y z →
      biInvariantDistance (multiply (group K) y x) (multiply (group K) z x) ≡
      biInvariantDistance y z

open SUNInvariantMetricAuthority public

sunInvariantLieMetric :
  ∀ {g a s} {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    {K : CompactSimpleLieGroup G 𝔤}
    {S : OrderedScalar Scalar} →
  SUNInvariantMetricAuthority K S → InvariantLieMetric K S
sunInvariantLieMetric authority = record
  { inner = traceInner authority
  ; norm = traceNorm authority
  ; distance = biInvariantDistance authority
  ; innerSymmetric = traceInnerSymmetric authority
  ; normNonnegative = traceNormNonnegative authority
  ; adjointIsometry = adjointTraceIsometry authority
  ; distanceLeftInvariant = distanceLeftInvariant authority
  ; distanceRightInvariant = distanceRightInvariant authority
  }

record SUNLocalChartAuthority
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar)
    (M : InvariantLieMetric K S) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    chartRadius : Scalar
    AlgebraSmall : 𝔤 → Set (a ⊔ s)
    GroupSmall : G → Set (g ⊔ s)

    expPreservesSmall : ∀ X → AlgebraSmall X → GroupSmall (exp K X)
    logPreservesSmall : ∀ x → GroupSmall x → AlgebraSmall (log K x)
    localLogExp : ∀ X → AlgebraSmall X → log K (exp K X) ≡ X
    localExpLog : ∀ x → GroupSmall x → exp K (log K x) ≡ x

    dexpConstant inverseDexpConstant : Scalar
    commutatorConstant adjointLipschitzConstant : Scalar

    DexpEstimate : Set (a ⊔ s)
    InverseDexpEstimate : Set (a ⊔ s)
    CommutatorEstimate : Set (a ⊔ s)
    AdjointLipschitzEstimate : Set (g ⊔ a ⊔ s)

    dexpEstimate : DexpEstimate
    inverseDexpEstimate : InverseDexpEstimate
    commutatorEstimate : CommutatorEstimate
    adjointLipschitzEstimate : AdjointLipschitzEstimate

open SUNLocalChartAuthority public

sunUniformLieChart :
  ∀ {g a s} {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    {K : CompactSimpleLieGroup G 𝔤}
    {S : OrderedScalar Scalar}
    {M : InvariantLieMetric K S} →
  SUNLocalChartAuthority K S M → UniformLieChart K S M
sunUniformLieChart authority = record
  { radius = chartRadius authority
  ; InAlgebraBall = AlgebraSmall authority
  ; InGroupBall = GroupSmall authority
  ; expMapsBall = expPreservesSmall authority
  ; logMapsBall = logPreservesSmall authority
  ; logExp = localLogExp authority
  ; expLog = localExpLog authority
  ; dexpNormBound = dexpConstant authority
  ; inverseDexpNormBound = inverseDexpConstant authority
  ; bracketNormConstant = commutatorConstant authority
  ; adjointLipschitzConstant = adjointLipschitzConstant authority
  ; DexpBound = DexpEstimate authority
  ; InverseDexpBound = InverseDexpEstimate authority
  ; BracketBound = CommutatorEstimate authority
  ; AdjointLipschitzBound = AdjointLipschitzEstimate authority
  ; dexpBound = dexpEstimate authority
  ; inverseDexpBound = inverseDexpEstimate authority
  ; bracketBound = commutatorEstimate authority
  ; adjointLipschitzBound = adjointLipschitzEstimate authority
  }

sunMetricAndChartAssemblyLevel : ProofLevel
sunMetricAndChartAssemblyLevel = machineChecked

sunMetricAndChartAuthorityLevel : ProofLevel
sunMetricAndChartAuthorityLevel = standardImported
