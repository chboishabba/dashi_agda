module DASHI.Core.MultiscaleMDL where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Exact, application-neutral multiscale carrier.

record MultiscaleCarrier : Set₁ where
  field
    Carrier : Nat → Set
    project : ∀ {j} → Carrier (suc j) → Carrier j
    lift : ∀ {j} → Carrier j → Carrier (suc j)
    project-lift : ∀ {j} (x : Carrier j) → project (lift x) ≡ x
open MultiscaleCarrier public

------------------------------------------------------------------------
-- Residual decomposition.

record ResidualCodec (tower : MultiscaleCarrier) : Set₁ where
  field
    Residual : Nat → Set
    residual :
      ∀ {j} →
      MultiscaleCarrier.Carrier tower (suc j) → Residual j
    reconstruct :
      ∀ {j} →
      MultiscaleCarrier.Carrier tower j →
      Residual j →
      MultiscaleCarrier.Carrier tower (suc j)
    reconstruct-project-residual :
      ∀ {j} (x : MultiscaleCarrier.Carrier tower (suc j)) →
      reconstruct
        (MultiscaleCarrier.project tower x)
        (residual x)
      ≡ x
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
  field
    kernel :
      ∀ j →
      MultiscaleCarrier.Carrier tower j →
      MultiscaleCarrier.Carrier tower j
    project-kernel :
      ∀ {j} (x : MultiscaleCarrier.Carrier tower (suc j)) →
      MultiscaleCarrier.project tower (kernel (suc j) x)
      ≡ kernel j (MultiscaleCarrier.project tower x)
open KernelTower public

------------------------------------------------------------------------
-- Symmetry quotient interface.

record SymmetryAction (tower : MultiscaleCarrier) : Set₁ where
  field
    Symmetry : Nat → Set
    identity : ∀ {j} → Symmetry j
    act :
      ∀ {j} →
      Symmetry j →
      MultiscaleCarrier.Carrier tower j →
      MultiscaleCarrier.Carrier tower j
    identity-act :
      ∀ {j} (x : MultiscaleCarrier.Carrier tower j) →
      act identity x ≡ x
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
