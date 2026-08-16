module DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushConventionCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Close the convention/order seam in the preferred equation-(0.11) lane at
-- the actual reduced su(2) operator-action level.  The CMP109 centre leg is
-- not an independently supplied matrix: by definition it is the left-log
-- inverse-dexp acting after the relative-product centre transport,
--
--       C_Y = J_+(Y) Ad_{exp Y}.
--
-- Once the standard dexp transport identity D_-(Y) Ad_{exp Y}=D_+(Y) and the
-- two inverse identities are supplied by the already-owned analytic
-- functional calculus, the finite reduced-adjoint cancellation theorem gives
--
--       C_Y = J_-(Y)
--
-- as an operator and therefore on every physical tangent vector.  This is the
-- exact sign/order convention needed by the printed differentiated Federbush
-- equation; there is no separate J/T majorisation and no Bishop-real to
-- rational-matrix equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra)
import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus as R
import DASHI.Physics.YangMills.BalabanCMP109FederbushDexpTransportCancellationExact as Cancel

record LiteralCMP109FederbushConvention (Y : SU2LieAlgebra) : Set where
  field
    dexpPlus dexpMinus inversePlus inverseMinus adjointTransport :
      R.ReducedAdjointOperator

    dexpMinusAfterAdjointIsPlus :
      R.composeReducedAdjoint Y dexpMinus adjointTransport ≡ dexpPlus

    inversePlusAfterPlusIsIdentity :
      R.composeReducedAdjoint Y inversePlus dexpPlus
      ≡ R.identityReducedAdjoint

    inverseMinusAfterMinusIsIdentity :
      R.composeReducedAdjoint Y inverseMinus dexpMinus
      ≡ R.identityReducedAdjoint

open LiteralCMP109FederbushConvention public

cancellationData :
  ∀ {Y} (convention : LiteralCMP109FederbushConvention Y) →
  Cancel.DexpTransportCancellationData Y
    (dexpPlus convention)
    (dexpMinus convention)
    (inversePlus convention)
    (inverseMinus convention)
    (adjointTransport convention)
cancellationData convention = record
  { Cancel.DexpTransportCancellationData.dexpMinusTransportIsPlus =
      dexpMinusAfterAdjointIsPlus convention
  ; Cancel.DexpTransportCancellationData.inversePlusTimesPlusIsIdentity =
      inversePlusAfterPlusIsIdentity convention
  ; Cancel.DexpTransportCancellationData.inverseMinusTimesMinusIsIdentity =
      inverseMinusAfterMinusIsIdentity convention
  }

printedCentreOperator :
  ∀ {Y} → LiteralCMP109FederbushConvention Y → R.ReducedAdjointOperator
printedCentreOperator {Y} convention =
  R.composeReducedAdjoint Y
    (inversePlus convention)
    (adjointTransport convention)

printedCentreOperatorIsOppositeInverseDexp :
  ∀ {Y} (convention : LiteralCMP109FederbushConvention Y) →
  printedCentreOperator convention ≡ inverseMinus convention
printedCentreOperatorIsOppositeInverseDexp {Y} convention =
  Cancel.inversePlusTransportIsInverseMinus
    Y
    (dexpPlus convention)
    (dexpMinus convention)
    (inversePlus convention)
    (inverseMinus convention)
    (adjointTransport convention)
    (cancellationData convention)

printedCentreActionIsOppositeInverseDexp :
  ∀ {Y} (convention : LiteralCMP109FederbushConvention Y)
    (variation : SU2LieAlgebra) →
  R.applyReducedAdjoint Y (printedCentreOperator convention) variation
  ≡ R.applyReducedAdjoint Y (inverseMinus convention) variation
printedCentreActionIsOppositeInverseDexp {Y} convention variation =
  cong (λ operator → R.applyReducedAdjoint Y operator variation)
    (printedCentreOperatorIsOppositeInverseDexp convention)

cmp109PhysicalFederbushConventionCancellationLevel : ProofLevel
cmp109PhysicalFederbushConventionCancellationLevel = machineChecked

cmp109PhysicalFederbushPrintedCentreActionLevel : ProofLevel
cmp109PhysicalFederbushPrintedCentreActionLevel = machineChecked
