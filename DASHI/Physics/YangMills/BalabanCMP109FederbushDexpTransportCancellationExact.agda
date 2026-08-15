module DASHI.Physics.YangMills.BalabanCMP109FederbushDexpTransportCancellationExact where

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
-- Expose the cancellation hidden by the earlier triangle estimate
--
--       J T - I = (J-I)T + (T-I).
--
-- For Y=log W, let D+ and D- be the left/right dexp operators, J+ and J-
-- their inverses, and T=Ad_W.  The standard Lie identity is
--
--       D- T = D+.
--
-- All five operators are analytic functions of ad_Y and therefore commute in
-- the reduced su(2) calculus.  Consequently
--
--       J+ T = J-.
--
-- This is much sharper than separately majorizing J+-I and T-I: the entire
-- physical Federbush component J+T has exactly the opposite-trivialization
-- inverse-dexp defect.  Hence the source |Y|<=1/12 conditioning problem should
-- spend only ONE inverse-dexp envelope, not a sum of two unrelated defects.
--
-- The proof below is purely finite operator algebra.  No analytic estimate,
-- determinant, or series convergence theorem is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using (SU2LieAlgebra)
import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus as R

record DexpTransportCancellationData
    (Y : SU2LieAlgebra)
    (dexpPlus dexpMinus inversePlus inverseMinus transport :
      R.ReducedAdjointOperator) : Set where
  field
    dexpMinusTransportIsPlus :
      R.composeReducedAdjoint Y dexpMinus transport ≡ dexpPlus

    inversePlusTimesPlusIsIdentity :
      R.composeReducedAdjoint Y inversePlus dexpPlus
      ≡ R.identityReducedAdjoint

    inverseMinusTimesMinusIsIdentity :
      R.composeReducedAdjoint Y inverseMinus dexpMinus
      ≡ R.identityReducedAdjoint

open DexpTransportCancellationData public

candidateTimesDexpMinusIsIdentity :
  ∀ Y dexpPlus dexpMinus inversePlus inverseMinus transport →
  DexpTransportCancellationData
    Y dexpPlus dexpMinus inversePlus inverseMinus transport →
  R.composeReducedAdjoint Y
    (R.composeReducedAdjoint Y inversePlus transport)
    dexpMinus
  ≡ R.identityReducedAdjoint
candidateTimesDexpMinusIsIdentity
    Y dexpPlus dexpMinus inversePlus inverseMinus transport dataSet =
  trans
    (R.composeReducedAssociative Y inversePlus transport dexpMinus)
    (trans
      (cong
        (R.composeReducedAdjoint Y inversePlus)
        (trans
          (R.composeReducedCommutative Y transport dexpMinus)
          (dexpMinusTransportIsPlus dataSet)))
      (inversePlusTimesPlusIsIdentity dataSet))

inversePlusTransportIsInverseMinus :
  ∀ Y dexpPlus dexpMinus inversePlus inverseMinus transport →
  DexpTransportCancellationData
    Y dexpPlus dexpMinus inversePlus inverseMinus transport →
  R.composeReducedAdjoint Y inversePlus transport ≡ inverseMinus
inversePlusTransportIsInverseMinus
    Y dexpPlus dexpMinus inversePlus inverseMinus transport dataSet =
  let
    candidate = R.composeReducedAdjoint Y inversePlus transport

    minusTimesInverseMinus :
      R.composeReducedAdjoint Y dexpMinus inverseMinus
      ≡ R.identityReducedAdjoint
    minusTimesInverseMinus = trans
      (R.composeReducedCommutative Y dexpMinus inverseMinus)
      (inverseMinusTimesMinusIsIdentity dataSet)

    candidateTimesMinus :
      R.composeReducedAdjoint Y candidate dexpMinus
      ≡ R.identityReducedAdjoint
    candidateTimesMinus =
      candidateTimesDexpMinusIsIdentity
        Y dexpPlus dexpMinus inversePlus inverseMinus transport dataSet
  in
  trans
    (sym (R.composeReducedIdentityRight Y candidate))
    (trans
      (cong
        (R.composeReducedAdjoint Y candidate)
        (sym minusTimesInverseMinus))
      (trans
        (sym (R.composeReducedAssociative
          Y candidate dexpMinus inverseMinus))
        (trans
          (cong
            (λ left → R.composeReducedAdjoint Y left inverseMinus)
            candidateTimesMinus)
          (R.composeReducedIdentityLeft Y inverseMinus))))

cmp109FederbushDexpTransportCancellationLevel : ProofLevel
cmp109FederbushDexpTransportCancellationLevel = machineChecked

-- Analytic/source identification still required: instantiate D+,D-,J+,J-,T
-- with the literal principal-log differential and Ad_{exp Y} conventions used
-- by CMP98/CMP109, including the sign of ad_Y.  Once that is done, the local
-- residual bound is an inverse-dexp bound at -Y, not a separate transport loss.
cmp109FederbushPhysicalDexpTransportIdentificationLevel : ProofLevel
cmp109FederbushPhysicalDexpTransportIdentificationLevel = conditional
