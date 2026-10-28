module DASHI.Mathematics.Topology.AlexanderHornedBinaryIcosahedralSpinSignBidiExact where

------------------------------------------------------------------------
-- A STRICTLY STRONGER OBSERVER THAN THE OLD A5 VOA QUOTIENT.
--
-- Classical group root: 2I = SL2(F5), with nonsplit center
--   1 -> {+/- I} -> 2I -> A5 -> 1.
-- New independent finite literal constructor/audit:
--   scripts/alexander_horned_spin_icosahedral_bridge.py
--
-- INPUT must provide one and the SAME source element x=m^3,
-- its spin image -I and its A5 image I. A BIDI consumer that
-- only observes the A5 projective image cannot recover spin
-- sign. This theorem is stronger than and compatible with
-- the older A5 quotient root-order-five non-descent.
--
-- The kernel of the source-to-spin homomorphism is still
-- not assumed trivial; neither the chosen spin quotient nor
-- source G has finite-order lifts by this fact alone.
--
-- Not an Agda enumeration of all SL2(F5) matrices and NOT
-- an identification with the Monster 3B state space.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record SpinProjectiveQuotient : Set₁ where
  field
    Source : Set
    Spin : Set
    Projective : Set

    sourceIdentity sourceMeridianCube : Source
    spinIdentity centralMinusOne : Spin
    projectiveIdentity : Projective

    spinImage : Source → Spin
    projective : Spin → Projective

    sourceIdentitySpin : spinImage sourceIdentity ≡ spinIdentity
    meridianCubeSpin : spinImage sourceMeridianCube ≡ centralMinusOne
    centralSpinSignNontrivial : centralMinusOne ≡ spinIdentity → ⊥

    projectSpinIdentity :
      projective spinIdentity ≡ projectiveIdentity
    projectKillsCentralSign :
      projective centralMinusOne ≡ projectiveIdentity

open SpinProjectiveQuotient public

projectiveImage : (Q : SpinProjectiveQuotient) → Source Q → Projective Q
projectiveImage Q x = projective Q (spinImage Q x)

spinObservable : (Q : SpinProjectiveQuotient) → Source Q → Spin Q
spinObservable Q = spinImage Q

cubeProjectivelyInvisible :
  (Q : SpinProjectiveQuotient) →
  projectiveImage Q (sourceMeridianCube Q)
    ≡ projectiveImage Q (sourceIdentity Q)
cubeProjectivelyInvisible Q =
  trans
    (cong (projective Q) (meridianCubeSpin Q))
    (trans
      (projectKillsCentralSign Q)
      (trans
        (sym (projectSpinIdentity Q))
        (sym (cong (projective Q) (sourceIdentitySpin Q)))))

cubeSpinSignIsVisible :
  (Q : SpinProjectiveQuotient) →
  spinImage Q (sourceMeridianCube Q)
    ≡ spinImage Q (sourceIdentity Q) → ⊥
cubeSpinSignIsVisible Q equal =
  centralSpinSignNontrivial Q
    (trans
      (sym (meridianCubeSpin Q))
      (trans equal (sourceIdentitySpin Q)))

noProjectiveRecoveryOfSpinObservable :
  (Q : SpinProjectiveQuotient) →
  Transport.ClaimTransport
    (projectiveImage Q) (spinObservable Q) → ⊥
noProjectiveRecoveryOfSpinObservable Q =
  Transport.claimNonTransportWitnessBlocksTransport
    (Descent.consumerNonDescentWitness
      (sourceMeridianCube Q)
      (sourceIdentity Q)
      (cubeProjectivelyInvisible Q)
      (cubeSpinSignIsVisible Q))

-- Exact finite witness supplier still needs connection to the
-- infinite tower. The Python script constructs levelwise
-- compatible commutator witnesses and demonstrates surjectivity
-- at depth 1; it is not an Agda kernel-level 120-element group.
