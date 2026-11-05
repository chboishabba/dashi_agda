module DASHI.Reasoning.Trialectic369T4ExteriorSquareExceptionalCrossPollinationExact where

------------------------------------------------------------------------
-- 369 T4 -> SYMPLECTIC EXTERIOR-SQUARE EXCEPTIONAL CROSS-POLLINATION
--
-- This owner connects two already-distinct repo surfaces:
--   (1) the literal punctured four-trit carrier with exact count 80;
--   (2) the derived oriented-Lagrangian bivector candidate with finite-script
--       count 80 and a same-action recognition interface to a 5D null cone.
--
-- Equal cardinality is retained as a comparison only.  The derived carrier is
-- constructed from T4 through symplectic/exterior-square structure and is not
-- identified with the raw punctured carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.RiemannQuarticPuncturedKernel4EnumerationExact as Raw
import DASHI.Foundations.Base369T4SymplecticExteriorSquareE6BridgeExact as Exterior

-- Re-export the existing proof receipt under the cross-pollination owner.
rawPuncturedT4CountIs80 = Raw.puncturedKernel4EnumerationLengthIs80

-- The derived count is currently an exact exhaustive-script receipt rather
-- than a kernel enumeration theorem, so only its pinned metadata is asserted.
derivedOrientedLagCountPinned :
  Exterior.orientedLagrangianBivectorCount ≡ 80
derivedOrientedLagCountPinned = refl

record Trialectic369T4ExteriorSquareCrossPollinationBoundary : Set where
  constructor trialectic-369-t4-exterior-square-cross-pollination-boundary
  field
    rawPuncturedT4ExactCountAvailable : Bool
    derivedLag80FiniteCertificateAvailable : Bool
    exteriorSquareRecognitionInterfaceAvailable : Bool
    sameNumberMeansSameCarrier : Bool
    sameNumberMeansSameAction : Bool
    rawT4AutomaticallyExceptional : Bool

canonicalTrialectic369T4ExteriorSquareCrossPollinationBoundary :
  Trialectic369T4ExteriorSquareCrossPollinationBoundary
canonicalTrialectic369T4ExteriorSquareCrossPollinationBoundary =
  trialectic-369-t4-exterior-square-cross-pollination-boundary
    true true true false false false
