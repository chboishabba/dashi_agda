module DASHI.Physics.Closure.NSPeriodicFarLowExactCommutatorIdentity where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicFarLowEnergyPairingCancellation as Energy
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact shell commutator identity.
--
-- The module performs only algebra.  It assumes the literal field-level split
--
--   Δ_j(a·∇v) = a·∇Δ_jv + [Δ_j,a·∇]v
--
-- and derives the tested energy identity using the self-pairing cancellation.
-- No multiplier estimate, absolute value, Schur bound, or Sobolev weight enters
-- this layer.
------------------------------------------------------------------------

record ShellCommutatorStructure
    {ℓ : Level}
    (Index Field Scalar : Set ℓ) : Set (lsuc ℓ) where
  field
    energy : Energy.PeriodicTransportEnergyStructure Field Scalar

    fieldAdd : Field → Field → Field
    shell : Index → Field → Field
    commutator : Index → Field → Field → Field

    projectedTransportSplit : ∀ j a v →
      shell j (Energy.transport energy a v)
      ≡ fieldAdd
          (Energy.transport energy a (shell j v))
          (commutator j a v)

    pairingAddLeft : ∀ x y z →
      Energy.pairing energy (fieldAdd x y) z
      ≡ Energy.scalarAdd energy
          (Energy.pairing energy x z)
          (Energy.pairing energy y z)

    scalarZeroLeft : ∀ x →
      Energy.scalarAdd energy (Energy.scalarZero energy) x ≡ x

open ShellCommutatorStructure public

exactFarLowCommutatorEnergyIdentity :
  ∀ {ℓ} {Index Field Scalar : Set ℓ} →
  (S : ShellCommutatorStructure Index Field Scalar) →
  ∀ j a v → Energy.DivergenceFree (energy S) a →
  Energy.pairing (energy S)
    (shell S j (Energy.transport (energy S) a v))
    (shell S j v)
  ≡
  Energy.pairing (energy S)
    (commutator S j a v)
    (shell S j v)
exactFarLowCommutatorEnergyIdentity S j a v divFree =
  trans
    (cong
      (λ projected →
        Energy.pairing (energy S) projected (shell S j v))
      (projectedTransportSplit S j a v))
    (trans
      (pairingAddLeft S
        (Energy.transport (energy S) a (shell S j v))
        (commutator S j a v)
        (shell S j v))
      (trans
        (cong
          (λ principal →
            Energy.scalarAdd (energy S) principal
              (Energy.pairing (energy S)
                (commutator S j a v)
                (shell S j v)))
          (Energy.homogeneousTransportCancellation
            (energy S) a (shell S j v) divFree))
        (scalarZeroLeft S
          (Energy.pairing (energy S)
            (commutator S j a v)
            (shell S j v)))))

farLowExactCommutatorIdentityLevel : ProofLevel
farLowExactCommutatorIdentityLevel = machineChecked
