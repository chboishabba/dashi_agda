module DASHI.Core.MultiscaleMDL where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Exact, application-neutral multiscale carrier.
--
-- This module isolates the checkable mathematical core shared by codec,
-- supervoxel, reasoning-field, and physics-facing readings.  It makes no
-- claim that a chosen carrier, cost, or kernel models nature.  Such claims
-- belong in explicitly gated bridge and empirical modules.

record MultiscaleCarrier : Set₁ where
  field
    Carrier : Nat → Set
    project : ∀ {j} → Carrier (suc j) → Carrier j
    lift : ∀ {j} → Carrier j → Carrier (suc j)
    project-lift : ∀ {j} (x : Carrier j) → project (lift x) ≡ x
open MultiscaleCarrier public

------------------------------------------------------------------------
-- Residual decomposition.
--
-- No additive structure is assumed.  A residual is whatever extra witness is
-- sufficient to reconstruct the fine state from its coarse projection.

record ResidualCodec (tower : MultiscaleCarrier) : Set₁ where
  open MultiscaleCarrier tower
  field
    Residual : Nat → Set
    residual : ∀ {j} → Carrier (suc j) → Residual j
    reconstruct : ∀ {j} → Carrier j → Residual j → Carrier (suc j)
    reconstruct-project-residual :
      ∀ {j} (x : Carrier (suc j)) →
      reconstruct (project x) (residual x) ≡ x
open ResidualCodec public

CoarseResidual :
  (tower : MultiscaleCarrier) →
  ResidualCodec tower →
  Nat → Set
CoarseResidual tower codec j =
  Σ (Carrier tower j) (λ _ → Residual codec j)

split :
  ∀ {tower : MultiscaleCarrier}
    (codec : ResidualCodec tower)
    {j} →
  Carrier tower (suc j) →
  CoarseResidual tower codec j
split {tower} codec x = project tower x , residual codec x

join :
  ∀ {tower : MultiscaleCarrier}
    (codec : ResidualCodec tower)
    {j} →
  CoarseResidual tower codec j →
  Carrier tower (suc j)
join codec (coarse , remainder) = reconstruct codec coarse remainder

join-split :
  ∀ {tower : MultiscaleCarrier}
    (codec : ResidualCodec tower)
    {j}
    (x : Carrier tower (suc j)) →
  join codec (split codec x) ≡ x
join-split codec x = reconstruct-project-residual codec x

------------------------------------------------------------------------
-- Scale-indexed kernels and exact naturality.

record KernelTower (tower : MultiscaleCarrier) : Set₁ where
  open MultiscaleCarrier tower
  field
    kernel : ∀ j → Carrier j → Carrier j
    project-kernel :
      ∀ {j} (x : Carrier (suc j)) →
      project (kernel (suc j) x) ≡ kernel j (project x)
open KernelTower public

-- A weaker quantitative commutation law can be layered on top once a metric
-- and an error carrier have been selected.  The exact law above is the clean
-- theorem spine; approximation is not silently identified with equality.

------------------------------------------------------------------------
-- Symmetry quotient interface.
--
-- Orbit equivalence is represented constructively by an explicit action
-- witness.  Formation of a quotient type is intentionally left to a chosen
-- setoid/quotient implementation rather than postulated here.

record SymmetryAction (tower : MultiscaleCarrier) : Set₁ where
  open MultiscaleCarrier tower
  field
    Symmetry : Nat → Set
    identity : ∀ {j} → Symmetry j
    act : ∀ {j} → Symmetry j → Carrier j → Carrier j
    identity-act : ∀ {j} (x : Carrier j) → act identity x ≡ x
open SymmetryAction public

record OrbitRelated
  {tower : MultiscaleCarrier}
  (symmetry : SymmetryAction tower)
  {j : Nat}
  (x y : Carrier tower j) : Set where
  constructor orbit-related
  field
    witness : Symmetry symmetry j
    witness-acts : act symmetry witness x ≡ y
open OrbitRelated public

------------------------------------------------------------------------
-- MDL accounting.
--
-- Costs are natural-number code lengths.  This gives exact accounting, not a
-- Shannon-optimality theorem.  Entropy/regret bounds require a probability
-- model and Kraft-style hypotheses and therefore remain separate obligations.

record MDLCost
  (tower : MultiscaleCarrier)
  (codec : ResidualCodec tower) : Set₁ where
  field
    coarseCost : ∀ {j} → Carrier tower j → Nat
    residualCost : ∀ {j} → Residual codec j → Nat
open MDLCost public

stepDescriptionLength :
  ∀ {tower : MultiscaleCarrier}
    {codec : ResidualCodec tower} →
  MDLCost tower codec →
  ∀ {j} → Carrier tower (suc j) → Nat
stepDescriptionLength {tower} {codec} cost x =
  coarseCost cost (project tower x) + residualCost cost (residual codec x)

step-description-is-coarse-plus-residual :
  ∀ {tower : MultiscaleCarrier}
    {codec : ResidualCodec tower}
    (cost : MDLCost tower codec)
    {j}
    (x : Carrier tower (suc j)) →
  stepDescriptionLength cost x ≡
  coarseCost cost (project tower x) + residualCost cost (residual codec x)
step-description-is-coarse-plus-residual cost x = refl

------------------------------------------------------------------------
-- Claim boundary.

record MDLClaimBoundary : Set where
  constructor mdl-claim-boundary
  field
    exactResidualReconstructionProved : Set
    entropyModelSupplied : Set
    kraftAdmissibilitySupplied : Set
    residualEntropyBoundProved : Set
    rateDistortionOptimalityProved : Set

-- The fields above are proposition slots rather than Boolean marketing flags:
-- a consumer must supply inhabitants of the claims it wishes to promote.
