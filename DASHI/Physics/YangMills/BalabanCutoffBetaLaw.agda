module DASHI.Physics.YangMills.BalabanCutoffBetaLaw where

-- Producer-side surface for the finite-cutoff coupling dynamics.  The
-- existing inverse-square step is deliberately an evaluated recurrence,
-- which is exactly what the budget arithmetic consumes.  This file records
-- the missing fact needed to *produce* that recurrence from Balaban's block
-- transformation: each correction is the value of a path-specialised
-- cutoff/scale beta law at the generated coupling, rather than an arbitrary
-- sequence.  CMP 109 I explicitly says that the displayed β_j(g_{j-1}) also
-- depends on the preceding generated couplings; that history is carried by
-- this whole `BalabanCutoffCouplingDynamics` witness, not erased by the final
-- scalar argument of `betaLaw`.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; suc; _<_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; absℝ ; _≤ℝ_ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; balaban-cmp-109 ; openTarget )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; coupling
  ; betaCorrection
  )

-- CMP 109 I, (1.20)--(1.22) and (5.42): the scale beta correction is
-- not a free scalar.  After the localized/infinite-volume representation of
-- the vacuum-polarization tensor Pi^(j), it is its off-diagonal second
-- momentum derivative, equivalently its coordinate moment.  The finite
-- position lists below deliberately keep the numerical approximation and its
-- tail certificate visible: a fixed finite-volume calculation alone cannot
-- inhabit this source identity.
sumℝ : {A : Set} → (A → ℝ) → List A → ℝ
sumℝ f [] = 0ℝ
sumℝ f (x ∷ xs) = f x +ℝ sumℝ f xs

-- The finite-torus calculation is useful only together with a quantitative
-- comparison to the localised infinite-volume coefficient.  CMP 99 (1985),
-- Theorems 3.1--3.4 and its generalized random-walk expansion provide the
-- propagator-decay/analyticity input; carrying it through the polarization
-- diagrams is still an owned theorem.  This record makes that latter bridge
-- an inequality rather than an opaque proposition.
record FiniteVolumeVacuumPolarisationTail
    (finiteMoment : ℕ → ℕ → ℝ)
    (infiniteVolumeMoment : ℕ → ℝ) : Set₁ where
  field
    -- The second natural-number argument is a finite-volume cutoff, distinct
    -- from the ultraviolet RG cutoff K of the surrounding dynamics.
    tailMajorant : ℕ → ℕ → ℝ

    tailMajorantNonnegative :
      ∀ scale volumeCutoff →
      0ℝ ≤ℝ tailMajorant scale volumeCutoff

    finiteVolumeMomentBound :
      ∀ scale volumeCutoff →
      absℝ
        (finiteMoment scale volumeCutoff
          -ℝ infiniteVolumeMoment scale)
      ≤ℝ tailMajorant scale volumeCutoff

    -- The exact topology/rate is deliberately deferred until the six-paper
    -- operator packet fixes the source norm and boundary convention.  It must
    -- nevertheless certify vanishing uniformly over all admitted scales and
    -- regular background configurations; a fixed-volume calculation is not
    -- sufficient.
    uniformTailVanishing : Set

open FiniteVolumeVacuumPolarisationTail public

-- A finite-cutoff version of Balaban's Theorem 2 only needs bounds that are
-- uniform in the finite volume.  Comparing with a distinguished
-- infinite-volume moment is one useful way to obtain those bounds, but is not
-- logically required by the coupling argument.  Keep both routes available.
record DirectFiniteVolumeBetaUniformity
    (finiteMoment : ℕ → ℕ → ℝ) : Set₁ where
  field
    betaLower betaUpper : ℝ

    betaLowerBound :
      ∀ scale volumeCutoff →
      betaLower ≤ℝ finiteMoment scale volumeCutoff

    betaUpperBound :
      ∀ scale volumeCutoff →
      finiteMoment scale volumeCutoff ≤ℝ betaUpper

    uniformityScope : Set

open DirectFiniteVolumeBetaUniformity public

data BetaVolumeUniformity
    (finiteMoment : ℕ → ℕ → ℝ) : Set₁ where
  directFiniteUniform :
    DirectFiniteVolumeBetaUniformity finiteMoment →
    BetaVolumeUniformity finiteMoment

  referenceCoefficientTail :
    (infiniteVolumeMoment : ℕ → ℝ) →
    FiniteVolumeVacuumPolarisationTail
      finiteMoment
      infiniteVolumeMoment →
    BetaVolumeUniformity finiteMoment

record BalabanVacuumPolarisationCoefficient
    (K : ℕ)
    (step : BalabanInverseSquareCouplingStep) : Set₁ where
  field
    Position : Set
    Direction : Set
    offDiagonal : Direction → Direction → Set
    μ ν : Direction
    μ≠ν : offDiagonal μ ν

    -- `finitePositions k volumeCutoff` is the explicit finite-volume carrier used
    -- by a certified calculation at RG scale k.  It is not silently
    -- identified with the source Z^d moment.
    finitePositions : ℕ → ℕ → List Position
    coordinate : Position → Direction → ℝ
    polarisation : ℕ → Direction → Direction → Position → ℝ

    finiteMoment : ℕ → ℕ → ℝ
    finiteMomentDefinition :
      ∀ k cutoff →
      finiteMoment k cutoff
        ≡
      sumℝ
        (λ x →
          polarisation k μ ν x
            *ℝ coordinate x μ
            *ℝ coordinate x ν)
        (finitePositions k cutoff)

    -- Balaban first takes the localized infinite-volume representation for
    -- (5.42).  The finite-cutoff Theorem 2 can instead consume direct bounds
    -- uniform in every torus, so no infinite-volume tail is forced here.
    infiniteVolumeMoment : ℕ → ℝ
    volumeUniformity : BetaVolumeUniformity finiteMoment

    -- This is the momentum-side normalization of CMP 109 I, (5.42): minus
    -- the off-diagonal second derivative of Pi at zero.  Keeping the minus
    -- sign in the field name prevents a later evaluator from silently using
    -- the opposite Fourier or bond-orientation convention.
    negativeOffDiagonalSecondMomentumDerivative : ℕ → ℝ
    momentEqualsNegativeSecondMomentumDerivative :
      ∀ k →
      infiniteVolumeMoment k
        ≡ negativeOffDiagonalSecondMomentumDerivative k

    -- This is (5.42), with the source's scale index aligned so that the
    -- recurrence correction at `suc k` is beta_{k+1}.
    betaFromVacuumPolarisation :
      ∀ k → k < K →
      betaCorrection step (suc k)
        ≡ negativeOffDiagonalSecondMomentumDerivative k

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanVacuumPolarisationCoefficient public

record BalabanCutoffCouplingDynamics (K : ℕ) : Set₁ where
  field
    step : BalabanInverseSquareCouplingStep

    -- `betaLaw k k<K g` is the source β_{k+1} correction for this already
    -- fixed generated history, evaluated at its distinguished current
    -- coupling argument.  It is not an assertion that β is autonomous in g.
    betaLaw : (k : ℕ) → k < K → ℝ → ℝ

    generatedBetaCorrection :
      ∀ k → (k<K : k < K) →
      betaCorrection step (suc k)
        ≡ betaLaw k k<K (coupling step k)

    -- The source-level coefficient identity is an independent field rather
    -- than prose attached to `betaLaw`.  It prevents a later implementation
    -- from certifying an arbitrary history-specialised scalar recurrence
    -- without exposing the vacuum-polarization calculation and its
    -- finite-volume tail obligation.
    vacuumPolarisationCoefficient :
      BalabanVacuumPolarisationCoefficient K step

    -- The inverse-square coordinate relation itself remains the explicit
    -- field of `step`; this witness says that it is the source coordinate,
    -- not merely a convenient numerical parametrisation.
    sourceCoordinateMeaning :
      BalabanInverseSquareCouplingStep.inverseSquareCoordinateMeaning step

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanCutoffCouplingDynamics public

-- CMP 109 I defines β_{j+1}(g_j) from the fluctuation effective action
-- (1.20)--(1.22).  Its introduction states that the four-dimensional tuned
-- small-coupling result (Theorem 2, pp. 258--260) needs a separate
-- perturbative proof.  Keep this producer unavailable until that exact
-- finite-cutoff estimate is extracted or proved.
actualBalabanCutoffCouplingDynamicsAvailable : Set
actualBalabanCutoffCouplingDynamicsAvailable = ⊥

currentBalabanCutoffBetaLawStatus : VerificationStatus
currentBalabanCutoffBetaLawStatus = openTarget
