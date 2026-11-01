module DASHI.Physics.Closure.NSPeriodicConcretePacketOffPartition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Order
import DASHI.Physics.Closure.NSPeriodicConcreteCompactGamma as Compact
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact numerator partition for packet fraction and off-packet fraction.
--
-- If packet energy is contained in total energy, then
--
--   E_packet + (E_total monus E_packet) = E_total.
--
-- Therefore the two exact ratios share a denominator and their numerators
-- partition it.  This is a conditional algebraic theorem; packet containment
-- for the literal dyadic packet remains a separate carrier fact.
------------------------------------------------------------------------

packetPlusComplementIsTotal :
  ∀ packet total →
  Order._≤ᴺ_ packet total →
  packet + Compact.monus total packet ≡ total
packetPlusComplementIsTotal zero total Order.z≤n = refl
packetPlusComplementIsTotal (suc packet) (suc total) (Order.s≤s contained) =
  cong suc (packetPlusComplementIsTotal packet total contained)

record PacketContainedInTotal
    (energy : Compact.ShellEnergy)
    (cutoff K : Nat) : Set where
  field
    packet-contained :
      Order._≤ᴺ_
        (Compact.packetEnergy energy K)
        (Compact.sumThrough energy cutoff)

open PacketContainedInTotal public

packetOffNumeratorsPartitionTotal :
  ∀ energy cutoff K →
  PacketContainedInTotal energy cutoff K →
  Compact.numerator (Compact.packetFraction energy cutoff K)
  + Compact.numerator (Compact.offPacketRatio energy cutoff K)
  ≡ Compact.sumThrough energy cutoff
packetOffNumeratorsPartitionTotal energy cutoff K contained =
  packetPlusComplementIsTotal
    (Compact.packetEnergy energy K)
    (Compact.sumThrough energy cutoff)
    (packet-contained contained)

packetAndOffShareDenominator :
  ∀ energy cutoff K →
  Compact.denominator (Compact.packetFraction energy cutoff K)
  ≡ Compact.denominator (Compact.offPacketRatio energy cutoff K)
packetAndOffShareDenominator energy cutoff K = refl

record ExactPacketOffPartition
    (energy : Compact.ShellEnergy)
    (cutoff K : Nat) : Set where
  field
    shared-denominator :
      Compact.denominator (Compact.packetFraction energy cutoff K)
      ≡ Compact.denominator (Compact.offPacketRatio energy cutoff K)

    numerator-partition :
      Compact.numerator (Compact.packetFraction energy cutoff K)
      + Compact.numerator (Compact.offPacketRatio energy cutoff K)
      ≡ Compact.sumThrough energy cutoff

open ExactPacketOffPartition public

exactPacketOffPartition :
  ∀ energy cutoff K →
  PacketContainedInTotal energy cutoff K →
  ExactPacketOffPartition energy cutoff K
exactPacketOffPartition energy cutoff K contained = record
  { shared-denominator = packetAndOffShareDenominator energy cutoff K
  ; numerator-partition =
      packetOffNumeratorsPartitionTotal energy cutoff K contained
  }

------------------------------------------------------------------------
-- Status: exact packet/off complement arithmetic is checked.  The remaining
-- carrier question is packet containment for the chosen literal packet and
-- cutoff convention, especially at the lowest shell where duplicate counting
-- must not be silently assumed away.
------------------------------------------------------------------------

concretePacketOffPartitionLevel : ProofLevel
concretePacketOffPartitionLevel = machineChecked
