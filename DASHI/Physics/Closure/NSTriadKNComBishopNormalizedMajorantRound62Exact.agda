module DASHI.Physics.Closure.NSTriadKNComBishopNormalizedMajorantRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Author: Zachary Murray.
-- Title: "Constructive Analysis in the Agda Proof Assistant".
-- arXiv:2205.08354; persistent identifier: 10.48550/arXiv.2205.08354.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 AUTHORITY BOUNDARY
--
-- This is the concrete Murray--Bishop SETOID comparison backend for normalized
-- Com majorants.  It proves the 17/64, 65/512 -> 133/256 aggregation directly
-- in Bishop.ℝ with rational constants embedded order-preservingly.
--
-- It is NOT, by itself, a same-object identification with the literal
-- `PeriodicHardShellFourierPDE.realField`: that older algebraic carrier uses
-- propositional equality, while Bishop.ℝ is governed by setoid equality.
-- The same-object physical B boundary is now
--
--   NSTriadKNComOrderedPhysicalMajorantRound62Exact
--
-- which keeps normalized energy in `Carrier (realField model)` and adds only an
-- ordered rational extension of that exact carrier.  A separate theorem would
-- be required to identify a particular literal Fourier model with this Bishop
-- backend.
--
-- The theorem here remains useful: whenever normalized energies are already in
-- Bishop.ℝ, same/adjacent majorants imply bandwidth-one energy <= embed(133/256)
-- without ever identifying the energy with Q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Rational.Base as Rat
open Rat using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as RationalGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as BishopCarrier

embed : ℚ → Bishop.ℝ
embed = BishopCarrier.bishopRationalEmbed

record BishopPhysicalNormalizedOddPQSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    normalizedPhysicalEnergy : Nat → Nat → Bishop.ℝ

    energyNonnegative : ∀ q r →
      Bishop._≤_ Bishop.0ℝ (normalizedPhysicalEnergy q r)

    inactiveEnergyZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      Bishop._≃_ (normalizedPhysicalEnergy q r) Bishop.0ℝ

    sameShellActiveBound : ∀ q →
      Hat.supportActive support q q ≡ true →
      Bishop._≤_
        (normalizedPhysicalEnergy q q)
        (embed RationalGram.sameShellTarget)

    forwardAdjacentActiveBound : ∀ q →
      Hat.supportActive support q (suc q) ≡ true →
      Bishop._≤_
        (normalizedPhysicalEnergy q (suc q))
        (embed RationalGram.adjacentShellTarget)

    reverseAdjacentActiveBound : ∀ q →
      Hat.supportActive support (suc q) q ≡ true →
      Bishop._≤_
        (normalizedPhysicalEnergy (suc q) q)
        (embed RationalGram.adjacentShellTarget)

open BishopPhysicalNormalizedOddPQSource public

samePairBelowEmbeddedTarget :
  (source : BishopPhysicalNormalizedOddPQSource) → ∀ q →
  Bishop._≤_
    (normalizedPhysicalEnergy source q q)
    (embed RationalGram.sameShellTarget)
samePairBelowEmbeddedTarget source q
  with Hat.supportActive (support source) q q in activeProof
... | true = sameShellActiveBound source q activeProof
... | false =
  BishopLaws.≤-respˡ-≃
    (inactiveEnergyZero source q q activeProof)
    (BishopCarrier.bishopEmbedOrder Aggregate.sameTargetNonnegative)

forwardAdjacentBelowEmbeddedTarget :
  (source : BishopPhysicalNormalizedOddPQSource) → ∀ q →
  Bishop._≤_
    (normalizedPhysicalEnergy source q (suc q))
    (embed RationalGram.adjacentShellTarget)
forwardAdjacentBelowEmbeddedTarget source q
  with Hat.supportActive (support source) q (suc q) in activeProof
... | true = forwardAdjacentActiveBound source q activeProof
... | false =
  BishopLaws.≤-respˡ-≃
    (inactiveEnergyZero source q (suc q) activeProof)
    (BishopCarrier.bishopEmbedOrder Aggregate.adjacentTargetNonnegative)

reverseAdjacentBelowEmbeddedTarget :
  (source : BishopPhysicalNormalizedOddPQSource) → ∀ q →
  Bishop._≤_
    (normalizedPhysicalEnergy source (suc q) q)
    (embed RationalGram.adjacentShellTarget)
reverseAdjacentBelowEmbeddedTarget source q
  with Hat.supportActive (support source) (suc q) q in activeProof
... | true = reverseAdjacentActiveBound source q activeProof
... | false =
  BishopLaws.≤-respˡ-≃
    (inactiveEnergyZero source (suc q) q activeProof)
    (BishopCarrier.bishopEmbedOrder Aggregate.adjacentTargetNonnegative)

bishopBandwidthOneEnergy :
  BishopPhysicalNormalizedOddPQSource → Nat → Bishop.ℝ
bishopBandwidthOneEnergy source q =
  Bishop._+_
    (Bishop._+_
      (normalizedPhysicalEnergy source q q)
      (normalizedPhysicalEnergy source q (suc q)))
    (normalizedPhysicalEnergy source (suc q) q)

embeddedThreeTargetMeaning :
  Bishop._≃_
    (Bishop._+_
      (Bishop._+_
        (embed RationalGram.sameShellTarget)
        (embed RationalGram.adjacentShellTarget))
      (embed RationalGram.adjacentShellTarget))
    (embed Aggregate.bandwidthOneTarget)
embeddedThreeTargetMeaning =
  let
    first :
      Bishop._≃_
        (Bishop._+_
          (embed RationalGram.sameShellTarget)
          (embed RationalGram.adjacentShellTarget))
        (embed
          (Rat._+_
            RationalGram.sameShellTarget
            RationalGram.adjacentShellTarget))
    first = BishopLaws.≃-symm
      (BishopCarrier.bishopEmbedAdd
        RationalGram.sameShellTarget RationalGram.adjacentShellTarget)

    second :
      Bishop._≃_
        (Bishop._+_
          (embed
            (Rat._+_
              RationalGram.sameShellTarget
              RationalGram.adjacentShellTarget))
          (embed RationalGram.adjacentShellTarget))
        (embed
          (Rat._+_
            (Rat._+_
              RationalGram.sameShellTarget
              RationalGram.adjacentShellTarget)
            RationalGram.adjacentShellTarget))
    second = BishopLaws.≃-symm
      (BishopCarrier.bishopEmbedAdd
        (Rat._+_
          RationalGram.sameShellTarget
          RationalGram.adjacentShellTarget)
        RationalGram.adjacentShellTarget)
  in
  subst
    (λ target →
      Bishop._≃_
        (Bishop._+_
          (Bishop._+_
            (embed RationalGram.sameShellTarget)
            (embed RationalGram.adjacentShellTarget))
          (embed RationalGram.adjacentShellTarget))
        (embed target))
    Aggregate.targetArithmetic
    (BishopLaws.≃-trans
      (BishopLaws.+-cong first BishopLaws.≃-refl)
      second)

bishopBandwidthOneBelowEmbedded133Over256 :
  (source : BishopPhysicalNormalizedOddPQSource) → ∀ q →
  Bishop._≤_
    (bishopBandwidthOneEnergy source q)
    (embed Aggregate.bandwidthOneTarget)
bishopBandwidthOneBelowEmbedded133Over256 source q =
  let
    summed :
      Bishop._≤_
        (bishopBandwidthOneEnergy source q)
        (Bishop._+_
          (Bishop._+_
            (embed RationalGram.sameShellTarget)
            (embed RationalGram.adjacentShellTarget))
          (embed RationalGram.adjacentShellTarget))
    summed =
      BishopLaws.+-mono-≤
        (BishopLaws.+-mono-≤
          (samePairBelowEmbeddedTarget source q)
          (forwardAdjacentBelowEmbeddedTarget source q))
        (reverseAdjacentBelowEmbeddedTarget source q)
  in
  BishopLaws.≤-respʳ-≃ embeddedThreeTargetMeaning summed

physicalComEnergyNeverIdentifiedWithRationalCarrier : Bool
physicalComEnergyNeverIdentifiedWithRationalCarrier = true

bishopBandwidthOneMajorantClosed : Bool
bishopBandwidthOneMajorantClosed = true

bishopEndpointIsLiteralFourierSameObject : Bool
bishopEndpointIsLiteralFourierSameObject = false

physicalComEnergyNeverIdentifiedWithRationalCarrierIsTrue :
  physicalComEnergyNeverIdentifiedWithRationalCarrier ≡ true
physicalComEnergyNeverIdentifiedWithRationalCarrierIsTrue = refl

bishopBandwidthOneMajorantClosedIsTrue :
  bishopBandwidthOneMajorantClosed ≡ true
bishopBandwidthOneMajorantClosedIsTrue = refl

bishopEndpointIsLiteralFourierSameObjectIsFalse :
  bishopEndpointIsLiteralFourierSameObject ≡ false
bishopEndpointIsLiteralFourierSameObjectIsFalse = refl
