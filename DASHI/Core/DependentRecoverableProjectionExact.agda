module DASHI.Core.DependentRecoverableProjectionExact where

------------------------------------------------------------------------
-- EXACT RECOVERABLE PROJECTIONS WITH STATE-DEPENDENT RESIDUAL TYPE
--
-- RecoverableQuotientCompositionExact uses one fixed Residual : Set.  That is
-- appropriate for uniform fibres, but it cannot express a quotient whose
-- residual rank/type varies with the coarse state without padding every stratum
-- into one global product.
--
-- This core makes the residual a family
--
--   Residual : Y -> Set
--
-- and therefore represents the exact code as the dependent sum
--
--   Sigma (y : Y), Residual y.
--
-- It is the generic owner for active-obligation fibres, p-adic/coarse-fine
-- residuals, and orbit-type quotients with stabilizer-dependent fibre size.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record DependentExactRecoverableProjection (X Y : Set) : Set₁ where
  constructor dependentExactRecoverableProjection
  field
    Residual : Y → Set
    project : X → Y
    residual : (x : X) → Residual (project x)
    reopen : (y : Y) → Residual y → X
    reopenExact : (x : X) → reopen (project x) (residual x) ≡ x

open DependentExactRecoverableProjection public

DependentCode :
  ∀ {X Y : Set} →
  DependentExactRecoverableProjection X Y → Set
DependentCode {Y = Y} projection = Σ Y (Residual projection)

encode :
  ∀ {X Y : Set}
    (projection : DependentExactRecoverableProjection X Y) →
  X → DependentCode projection
encode projection x = project projection x , residual projection x

decode :
  ∀ {X Y : Set}
    (projection : DependentExactRecoverableProjection X Y) →
  DependentCode projection → X
decode projection (y , r) = reopen projection y r

decodeEncodeExact :
  ∀ {X Y : Set}
    (projection : DependentExactRecoverableProjection X Y)
    (x : X) →
  decode projection (encode projection x) ≡ x
decodeEncodeExact projection = reopenExact projection

DependentCodeSeparating :
  ∀ {X Y : Set}
    (projection : DependentExactRecoverableProjection X Y) → Set
DependentCodeSeparating {X = X} projection =
  (x y : X) → encode projection x ≡ encode projection y → x ≡ y

dependentCodeSeparating :
  ∀ {X Y : Set}
    (projection : DependentExactRecoverableProjection X Y) →
  DependentCodeSeparating projection
dependentCodeSeparating projection x y same =
  trans
    (sym (decodeEncodeExact projection x))
    (trans
      (cong (decode projection) same)
      (decodeEncodeExact projection y))

------------------------------------------------------------------------
-- Uniform residuals embed as the constant-family special case.
------------------------------------------------------------------------

record UniformRecoverableProjection (X Y : Set) : Set₁ where
  constructor uniformRecoverableProjection
  field
    UniformResidual : Set
    uniformProject : X → Y
    uniformResidual : X → UniformResidual
    uniformReopen : Y → UniformResidual → X
    uniformReopenExact :
      (x : X) → uniformReopen (uniformProject x) (uniformResidual x) ≡ x

open UniformRecoverableProjection public

uniformAsDependent :
  ∀ {X Y : Set} →
  UniformRecoverableProjection X Y →
  DependentExactRecoverableProjection X Y
uniformAsDependent uniform =
  dependentExactRecoverableProjection
    (λ _ → UniformResidual uniform)
    (uniformProject uniform)
    (uniformResidual uniform)
    (uniformReopen uniform)
    (uniformReopenExact uniform)

------------------------------------------------------------------------
-- Boundary: a dependent residual family need not be replaced by a padded
-- global product merely to fit the reconstruction interface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record DependentRecoverableProjectionBoundary : Set where
  constructor dependentRecoverableProjectionBoundary
  field
    residualTypeMayDependOnCoarseState : Bool
    exactReconstructionStillAvailable : Bool
    dependentCodeIsSeparating : Bool
    uniformResidualIsSpecialCase : Bool
    dependentResidualMustBePaddedToGlobalProduct : Bool

canonicalDependentRecoverableProjectionBoundary :
  DependentRecoverableProjectionBoundary
canonicalDependentRecoverableProjectionBoundary =
  dependentRecoverableProjectionBoundary true true true true false
