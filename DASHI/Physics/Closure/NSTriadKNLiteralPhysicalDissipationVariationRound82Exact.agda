module DASHI.Physics.Closure.NSTriadKNLiteralPhysicalDissipationVariationRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND82 / EXACT WEIGHTED DISSIPATION POLARIZATION
--
-- `LiteralPhysicalCompactTransferDriftRound82Exact` defines the selected
-- packet dissipation from the SAME |k|^2 weight that appears in the literal
-- viscous RHS.  This module proves the corresponding quadratic expansion rather
-- than merely recording the product-rule-shaped tangent:
--
--   D(u+v) = D(u) + Ddot(u)[v] + D(v),
--
-- where
--
--   Ddot(u)[v]
--     = <v_K, |k|^2 u_K> + <u_K, |k|^2 v_K>.
--
-- Everything is finite Hermitian algebra on the hard packet.  No continuum
-- differentiation or function extensionality is used.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Physical

finitePairingCongruence :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left left′ right right′ : Z3.FourierMode → C3.Complex3 F) →
  (∀ mode → left mode ≡ left′ mode) →
  (∀ mode → right mode ≡ right′ mode) →
  Packet.finiteHermitianPairing modes left right
  ≡ Packet.finiteHermitianPairing modes left′ right′
finitePairingCongruence [] left left′ right right′ leftEq rightEq = refl
finitePairingCongruence (mode ∷ rest) left left′ right right′ leftEq rightEq =
  cong₂ C3.complexAdd
    (cong₂ C3.hermitianPairing3 (leftEq mode) (rightEq mode))
    (finitePairingCongruence rest left left′ right right′ leftEq rightEq)

weightedDissipationPairing :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Physical.LiteralPhysicalCompactTransferDatum model) →
  (Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  C3.Complex (LP.realField model)
weightedDissipationPairing {model = model} datum field =
  Packet.finiteHermitianPairing
    (Physical.packetModes datum)
    (Packet.packetField model (Physical.shell datum) field)
    (Physical.weightedPacketField datum field)

weightedDissipationFirstVariation :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Physical.LiteralPhysicalCompactTransferDatum model) →
  (base tangent : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  C3.Complex (LP.realField model)
weightedDissipationFirstVariation {model = model} datum base tangent =
  C3.complexAdd
    (Packet.finiteHermitianPairing
      (Physical.packetModes datum)
      (Packet.packetField model (Physical.shell datum) tangent)
      (Physical.weightedPacketField datum base))
    (Packet.finiteHermitianPairing
      (Physical.packetModes datum)
      (Packet.packetField model (Physical.shell datum) base)
      (Physical.weightedPacketField datum tangent))

weightedDissipationQuadraticRemainder :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Physical.LiteralPhysicalCompactTransferDatum model) →
  (tangent : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  C3.Complex (LP.realField model)
weightedDissipationQuadraticRemainder datum tangent =
  weightedDissipationPairing datum tangent

weightedDissipationPolarizationExact :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Physical.LiteralPhysicalCompactTransferDatum model)
    (base tangent : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  weightedDissipationPairing datum (First.fieldAdd base tangent)
  ≡
  C3.complexAdd
    (C3.complexAdd
      (weightedDissipationPairing datum base)
      (weightedDissipationFirstVariation datum base tangent))
    (weightedDissipationQuadraticRemainder datum tangent)
weightedDissipationPolarizationExact {model = model} datum base tangent =
  let
    modes = Physical.packetModes datum
    packetBase = Packet.packetField model (Physical.shell datum) base
    packetTangent = Packet.packetField model (Physical.shell datum) tangent
    weightBase = Physical.weightedPacketField datum base
    weightTangent = Physical.weightedPacketField datum tangent

    packetSum = Packet.packetField model (Physical.shell datum)
      (First.fieldAdd base tangent)
    weightSum = Physical.weightedPacketField datum
      (First.fieldAdd base tangent)

    firstRewrite :
      Packet.finiteHermitianPairing modes packetSum weightSum
      ≡ Packet.finiteHermitianPairing modes
          (First.fieldAdd packetBase packetTangent)
          (First.fieldAdd weightBase weightTangent)
    firstRewrite = finitePairingCongruence modes
      packetSum (First.fieldAdd packetBase packetTangent)
      weightSum (First.fieldAdd weightBase weightTangent)
      (Physical.packetFieldAdd model (Physical.shell datum) base tangent)
      (Physical.weightedPacketFieldAdd datum base tangent)

    expanded :
      Packet.finiteHermitianPairing modes
        (First.fieldAdd packetBase packetTangent)
        (First.fieldAdd weightBase weightTangent)
      ≡
      C3.complexAdd
        (C3.complexAdd
          (Packet.finiteHermitianPairing modes packetBase weightBase)
          (Packet.finiteHermitianPairing modes packetBase weightTangent))
        (C3.complexAdd
          (Packet.finiteHermitianPairing modes packetTangent weightBase)
          (Packet.finiteHermitianPairing modes packetTangent weightTangent))
    expanded =
      trans
        (Packet.finiteHermitianPairingAddLeft
          modes packetBase packetTangent (First.fieldAdd weightBase weightTangent))
        (cong₂ C3.complexAdd
          (Packet.finiteHermitianPairingAddRight
            modes packetBase weightBase weightTangent)
          (Packet.finiteHermitianPairingAddRight
            modes packetTangent weightBase weightTangent))

    bb = Packet.finiteHermitianPairing modes packetBase weightBase
    bt = Packet.finiteHermitianPairing modes packetBase weightTangent
    tb = Packet.finiteHermitianPairing modes packetTangent weightBase
    tt = Packet.finiteHermitianPairing modes packetTangent weightTangent

    regroup :
      C3.complexAdd (C3.complexAdd bb bt) (C3.complexAdd tb tt)
      ≡ C3.complexAdd (C3.complexAdd bb (C3.complexAdd tb bt)) tt
    regroup =
      trans
        (Packet.complexInterchange bb bt tb tt)
        (trans
          (Field.complexAddAssociative bb tb (C3.complexAdd bt tt))
          (trans
            (cong (C3.complexAdd bb)
              (sym (Field.complexAddAssociative tb bt tt)))
            (sym
              (Field.complexAddAssociative
                bb (C3.complexAdd tb bt) tt))))
  in
  trans firstRewrite (trans expanded regroup)

round82LiteralWeightedDissipationFirstVariationDerived : Bool
round82LiteralWeightedDissipationFirstVariationDerived = true

round82LiteralWeightedDissipationPolarizationExact : Bool
round82LiteralWeightedDissipationPolarizationExact = true

round82LiteralWeightedDissipationPolarizationExactIsTrue :
  round82LiteralWeightedDissipationPolarizationExact ≡ true
round82LiteralWeightedDissipationPolarizationExactIsTrue = refl
