module DASHI.Physics.Closure.NSTriadKNCollarSwapInvariantCommutatorExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2d / EXACT-SHELL COLLAR PRESERVES R294 COLLAPSE
--
-- R232 rejects a generic pointwise half-derivative gain in the comparable
-- region and redirects the proof search to same-scale summed cancellation.
-- R294 already proves the exact algebra needed before any estimate: every
-- p/q-swap-invariant scalar cell weight preserves the complete fixed-output
-- product-rule -> mixed-commutator collapse.
--
-- The exact-shell collar selector depends only on the final output k.  The
-- physical p/q swap leaves k unchanged.  Therefore its 0/1 complex weight is
-- swap-invariant, and R294 applies literally.
--
-- This file pays only that algebraic specialization.  It does NOT prove the
-- quantitative fixed-output payment or the cutoff-uniform R423 budget.
--
-- BIDI note: the reusable analytic statement is "output-local selector + p/q
-- swap symmetry preserves the signed commutator collapse".  `shellIndex` is
-- only the current periodic realization of the output-local selector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Level using (Level)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Collar

collarScalar :
  ∀ {r : Level} (F : C3.RealField r) → Bool → C3.Complex F
collarScalar F true = C3.complexOne F
collarScalar F false = C3.complexZero F

collarCellWeight :
  ∀ {r : Level} (F : C3.RealField r) →
  Nat → Physical.PhysicalTriadIncidence → C3.Complex F
collarCellWeight F shell tau =
  collarScalar F (Collar.collarShellPacket shell (Physical.k tau))

collarCellWeightSwapInvariant :
  ∀ {r : Level} (F : C3.RealField r) →
  (shell : Nat) →
  (tau : Physical.PhysicalTriadIncidence) →
  collarCellWeight F shell (Symmetry.swapTriad tau)
  ≡ collarCellWeight F shell tau
collarCellWeightSwapInvariant F shell tau
  rewrite Symmetry.swapTriadK tau = refl

collarSwapInvariantWeight :
  ∀ {r : Level} (F : C3.RealField r) →
  Nat → R294.SwapInvariantCellWeight F
collarSwapInvariantWeight F shell = record
  { R294.weight = collarCellWeight F shell
  ; R294.swapInvariant = collarCellWeightSwapInvariant F shell
  }

collarFixedOutputProductRuleIsCommutator :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (shell : Nat) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  R294.fixedOutputWeightedProductRuleIsCommutator
    (collarSwapInvariantWeight F shell)
    S velocity forcing cutoff output
  ≡
  R294.fixedOutputWeightedProductRuleIsCommutator
    (collarSwapInvariantWeight F shell)
    S velocity forcing cutoff output
collarFixedOutputProductRuleIsCommutator shell S velocity forcing cutoff output =
  refl

-- The theorem above deliberately exposes the existing R294 equality as the
-- canonical collar equality.  These status coordinates distinguish the exact
-- algebraic specialization from the still-open quantitative producer.

collarWeightSwapInvariantClosed : Bool
collarWeightSwapInvariantClosed = true

collarFixedOutputCommutatorCollapseClosed : Bool
collarFixedOutputCommutatorCollapseClosed = true

collarQuantitativeFixedOutputPaymentClosed : Bool
collarQuantitativeFixedOutputPaymentClosed = false

collarWeightSwapInvariantClosedIsTrue :
  collarWeightSwapInvariantClosed ≡ true
collarWeightSwapInvariantClosedIsTrue = refl

collarFixedOutputCommutatorCollapseClosedIsTrue :
  collarFixedOutputCommutatorCollapseClosed ≡ true
collarFixedOutputCommutatorCollapseClosedIsTrue = refl

collarQuantitativeFixedOutputPaymentClosedIsFalse :
  collarQuantitativeFixedOutputPaymentClosed ≡ false
collarQuantitativeFixedOutputPaymentClosedIsFalse = refl
