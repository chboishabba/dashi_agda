module DASHI.Geometry.SSP369KernelStability where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties as NatP

open import DASHI.Geometry.SSP369Ultrametric

------------------------------------------------------------------------
-- Kernel stability over the existing 369 prefix ultrametric.
--
-- The repository's distance is depth minus common-prefix agreement.  Hence a
-- kernel that never destroys prefix agreement is non-expanding.  This is the
-- precise checked content behind the weaker phrase "stable arms".

_≢_ : {A : Set} → A → A → Set
_≢_ x y = x ≡ y → ⊥

record PrefixMonotoneKernel (d : Nat) : Set where
  constructor prefix-monotone-kernel
  field
    apply : Address d → Address d
    preservesAgreement :
      ∀ x y → agreementDepth x y ≤ agreementDepth (apply x) (apply y)
open PrefixMonotoneKernel public

distance-nonexpanding :
  ∀ {d}
    (K : PrefixMonotoneKernel d)
    (x y : Address d) →
  distance (apply K x) (apply K y) ≤ distance x y
distance-nonexpanding {d} K x y =
  NatP.∸-monoʳ-≤ d (preservesAgreement K x y)

record StrictPrefixContractingKernel (d : Nat) : Set where
  constructor strict-prefix-contracting-kernel
  field
    monotoneKernel : PrefixMonotoneKernel d
    contractsDistinct :
      ∀ x y → x ≢ y →
      distance (apply monotoneKernel x) (apply monotoneKernel y) < distance x y
open StrictPrefixContractingKernel public

strict-kernel-contracts-distance :
  ∀ {d}
    (K : StrictPrefixContractingKernel d)
    (x y : Address d) →
    x ≢ y →
  distance (apply (monotoneKernel K) x) (apply (monotoneKernel K) y) <
  distance x y
strict-kernel-contracts-distance K x y x≢y = contractsDistinct K x y x≢y

------------------------------------------------------------------------
-- Exact scale-compatibility receipt for address kernels.
--
-- The generic multiscale core uses project-kernel naturality.  Here the same
-- idea is exposed for any selected parent map between fixed address depths.

record AddressKernelNaturality (coarseDepth fineDepth : Nat) : Set where
  constructor address-kernel-naturality
  field
    parent : Address fineDepth → Address coarseDepth
    coarseKernel : Address coarseDepth → Address coarseDepth
    fineKernel : Address fineDepth → Address fineDepth
    parent-kernel :
      ∀ x → parent (fineKernel x) ≡ coarseKernel (parent x)
open AddressKernelNaturality public

------------------------------------------------------------------------
-- Identity witness: useful as a compile-time regression and as the neutral
-- element for later compositions.

identityPrefixKernel : ∀ {d} → PrefixMonotoneKernel d
identityPrefixKernel =
  prefix-monotone-kernel
    (λ x → x)
    (λ x y → NatP.≤-reflexive refl)

identity-distance-stable :
  ∀ {d} (x y : Address d) →
  distance (apply identityPrefixKernel x) (apply identityPrefixKernel y) ≡
  distance x y
identity-distance-stable x y = refl

------------------------------------------------------------------------
-- Boundary: non-expansion is proved above.  Unique fixed points do not follow
-- from non-expansion alone.  A fixed-point theorem additionally needs strict
-- contraction plus a suitable completeness/finite-descent argument; this
-- module deliberately does not smuggle either premise into the conclusion.
