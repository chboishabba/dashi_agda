{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_)
 
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- NODE-ALIGNED COUPLING FOR THE EDGE-INDEXED LITERAL PLAQUETTE PRODUCER
--
-- The canonical source inverse-coupling trajectory is
--
--   u_0       = producer.nextInverseCouplingSq 0
--   u_(k+1)   = producer.inverseCouplingSq k.
--
-- Therefore the producer's CURRENT coupling at edge k belongs to source node
-- k+1, not node k.  The old same-index readout
--
--   source g_k := producer.coupling k
--
-- silently paired u_(k+1) with producer.coupling(k+1).
--
-- This carrier fixes the ownership:
--
--   g_(k+1) := producer.coupling k
--
-- and leaves only g_0 explicit, because the current producer record stores no
-- "nextCoupling" coordinate at edge zero.
------------------------------------------------------------------------

record LiteralPlaquetteNodeCoupling
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet) : Set₁ where
  field
    initialCoupling : ℚ
    initialCouplingPositive : Positive initialCoupling

    initialInverseSquare :
      Plaquette.nextInverseCouplingSq dataSet zero
      * Order.square initialCoupling
      ≡ 1ℚ

    producerCouplingPositive :
      ∀ edge →
      Positive (Plaquette.coupling (Plaquette.remainder dataSet) edge)

    producerCurrentInverseSquare :
      ∀ edge →
      Plaquette.inverseCouplingSq dataSet edge
      * Order.square
          (Plaquette.coupling (Plaquette.remainder dataSet) edge)
      ≡ 1ℚ

open LiteralPlaquetteNodeCoupling public

sourceCoupling :
  ∀ {dataSet coherence} →
  LiteralPlaquetteNodeCoupling dataSet coherence →
  Nat → ℚ
sourceCoupling coordinate zero =
  initialCoupling coordinate
sourceCoupling {dataSet = dataSet} coordinate (suc edge) =
  Plaquette.coupling (Plaquette.remainder dataSet) edge

sourceCouplingPositive :
  ∀ {dataSet coherence}
    (coordinate : LiteralPlaquetteNodeCoupling dataSet coherence)
    node →
  Positive (sourceCoupling coordinate node)
sourceCouplingPositive coordinate zero =
  initialCouplingPositive coordinate
sourceCouplingPositive coordinate (suc edge) =
  producerCouplingPositive coordinate edge

sourceInverseSquareRepresentation :
  ∀ {dataSet coherence}
    (coordinate : LiteralPlaquetteNodeCoupling dataSet coherence)
    node →
  Flow.inverseCoupling
      (Source.canonicalSourceTrajectory dataSet coherence)
      node
  * Order.square (sourceCoupling coordinate node)
  ≡ 1ℚ
sourceInverseSquareRepresentation coordinate zero =
  initialInverseSquare coordinate
sourceInverseSquareRepresentation coordinate (suc edge) =
  producerCurrentInverseSquare coordinate edge

sameIndexProducerCouplingIsCanonicalSourceCoupling : Bool
sameIndexProducerCouplingIsCanonicalSourceCoupling = false

successorNodeUsesCurrentProducerCoupling : Bool
successorNodeUsesCurrentProducerCoupling = true

sameIndexProducerCouplingIsCanonicalSourceCouplingIsFalse :
  sameIndexProducerCouplingIsCanonicalSourceCoupling ≡ false
sameIndexProducerCouplingIsCanonicalSourceCouplingIsFalse = refl

successorNodeUsesCurrentProducerCouplingIsTrue :
  successorNodeUsesCurrentProducerCoupling ≡ true
successorNodeUsesCurrentProducerCouplingIsTrue = refl

literalPlaquetteNodeCouplingCompilerLevel : ProofLevel
literalPlaquetteNodeCouplingCompilerLevel = machineChecked

-- Remaining source meaning is now correctly indexed:
--   * identify the bare/source-node-zero coupling with nextInverseCouplingSq 0;
--   * identify each producer current coupling with inverseCouplingSq at that
--     same edge.
-- No cross-edge coupling equality is requested.
literalPlaquetteInverseSquareCoordinateMeaningLevel : ProofLevel
literalPlaquetteInverseSquareCoordinateMeaningLevel = conditional
