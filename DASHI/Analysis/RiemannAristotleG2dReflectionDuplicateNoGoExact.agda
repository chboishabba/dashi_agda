module DASHI.Analysis.RiemannAristotleG2dReflectionDuplicateNoGoExact where

------------------------------------------------------------------------
-- G2d / REFLECTION-ONLY CANCELLATION NO-GO
--
-- The literal finite near carrier is reflection-stable, but each stored
-- offPairTerm already contains sigma + R sigma.  Hence the stored paired cell
-- is reflection-invariant:
--
--   v_(R sigma) = v_sigma.
--
-- Therefore a non-fixed reflection orbit contributes
--
--   <v_sigma,v_(R sigma)> = <v_sigma,v_sigma>,
--
-- which is positive whenever the surviving post-Schur cell has positive energy.
-- Reflection has already paid for cancellation of the odd sinh*sin channel;
-- it cannot, by itself, force the remaining Gram debt nonpositive.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

record ReflectionDuplicateSurface : Set₁ where
  constructor reflection-duplicate-surface
  field
    Index Cell Scalar : Set
    reflect : Index → Index
    cell : Index → Cell
    dot : Cell → Cell → Scalar
    positive : Scalar → Set

    reflectCellInvariant : ∀ i → cell (reflect i) ≡ cell i

open ReflectionDuplicateSurface public

reflectionCrossEqualsDiagonal :
  (S : ReflectionDuplicateSurface) →
  (i : Index S) →
  dot S (cell S i) (cell S (reflect S i))
  ≡ dot S (cell S i) (cell S i)
reflectionCrossEqualsDiagonal S i =
  cong (dot S (cell S i)) (reflectCellInvariant S i)

reflectionCrossPositiveWhenDiagonalPositive :
  (S : ReflectionDuplicateSurface) →
  (i : Index S) →
  positive S (dot S (cell S i) (cell S i)) →
  positive S (dot S (cell S i) (cell S (reflect S i)))
reflectionCrossPositiveWhenDiagonalPositive S i h
  rewrite reflectionCrossEqualsDiagonal S i = h

record G2dReflectionNoGoBoundary : Set where
  constructor g2d-reflection-no-go-boundary
  field
    reflectionAlreadyUsedToCancelOddKernelChannel : Bool
    reflectionAlreadyUsedToCancelOddKernelChannelIsTrue :
      reflectionAlreadyUsedToCancelOddKernelChannel ≡ true

    pairedFiniteCellReflectionInvariant : Bool
    pairedFiniteCellReflectionInvariantIsTrue :
      pairedFiniteCellReflectionInvariant ≡ true

    reflectionAloneForcesGramDebtNonpositive : Bool
    reflectionAloneForcesGramDebtNonpositiveIsFalse :
      reflectionAloneForcesGramDebtNonpositive ≡ false

    additionalOrdinateCancellationInputRequired : Bool
    additionalOrdinateCancellationInputRequiredIsTrue :
      additionalOrdinateCancellationInputRequired ≡ true

canonicalG2dReflectionNoGoBoundary : G2dReflectionNoGoBoundary
canonicalG2dReflectionNoGoBoundary =
  g2d-reflection-no-go-boundary
    true refl
    true refl
    false refl
    true refl
