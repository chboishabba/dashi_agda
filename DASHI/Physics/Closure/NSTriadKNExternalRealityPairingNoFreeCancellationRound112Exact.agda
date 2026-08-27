module DASHI.Physics.Closure.NSTriadKNExternalRealityPairingNoFreeCancellationRound112Exact where

------------------------------------------------------------------------
-- ROUND112 / REALITY CONJUGATION IS NOT A FREE SIGN CANCELLATION
--
-- A tempting external-network shortcut is to pair each physical incidence with
-- its lattice-conjugate reality mate and hope the signed transfer cancels.
-- The repository's exact physical theorem says the opposite sign geometry:
--
--   T(conjugate tau) = T(tau).
--
-- Thus the conjugate pair contributes
--
--   T(tau) + T(conjugate tau) = T(tau) + T(tau),
--
-- not a difference.  Reality closure is essential for physical reconstruction,
-- but by itself supplies no antisymmetric cancellation of the external signed
-- transfer.  Any gain must come from another reindexing (such as the ordered
-- energy mate), a commutator, or packet/phase dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy

realityConjugatePairIsDoubleBaseTransfer :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode →
      C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (Audit.orderedSignedTransferAt E I tau velocity)
    (Audit.orderedSignedTransferAt E I (Symmetry.conjugateTriad tau) velocity)
  ≡
  C3.complexAdd
    (Audit.orderedSignedTransferAt E I tau velocity)
    (Audit.orderedSignedTransferAt E I tau velocity)
realityConjugatePairIsDoubleBaseTransfer
    E I velocity reality divergenceFree tau =
  cong
    (C3.complexAdd (Audit.orderedSignedTransferAt E I tau velocity))
    (Energy.orderedTransferConjugateInvariant
      E I velocity reality divergenceFree tau)

round112RealityConjugationProvidesAntisymmetricTransfer : Bool
round112RealityConjugationProvidesAntisymmetricTransfer = false

round112RealityConjugateTransferIsInvariant : Bool
round112RealityConjugateTransferIsInvariant = true

round112RealityConjugationProvidesAntisymmetricTransferIsFalse :
  round112RealityConjugationProvidesAntisymmetricTransfer ≡ false
round112RealityConjugationProvidesAntisymmetricTransferIsFalse = refl

round112RealityConjugateTransferIsInvariantIsTrue :
  round112RealityConjugateTransferIsInvariant ≡ true
round112RealityConjugateTransferIsInvariantIsTrue = refl
