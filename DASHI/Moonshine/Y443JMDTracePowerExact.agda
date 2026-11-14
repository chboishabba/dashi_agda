module DASHI.Moonshine.Y443JMDTracePowerExact where

------------------------------------------------------------------------
-- JMD / James Michael DuPont (meta-introspector) trace steps 2--4.
--
-- The external report describes w = x4 * beta of order 10 and the
-- recovered path generators x4 = w^5, beta = w^6.
--
-- DASHI proves the useful generic consequence: a certified u/v word
-- for w yields certified u/v words for x4 and beta. This does not
-- synthesize the absent w word or the remaining eight path lemmas.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

groupPower :
  ∀ {G} (gi : TM.GroupWithInverse G) →
  G → Nat → G
groupPower gi x zero = Pair.identity gi
groupPower gi x (suc n) =
  Pair.multiply gi x (groupPower gi x n)

powerRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (u v w : G) (n : Nat) →
  Pair.RepresentedByPair gi u v w →
  Pair.RepresentedByPair gi u v (groupPower gi w n)
powerRepresented gi u v w zero rw =
  Pair.identityRepresented gi u v
powerRepresented gi u v w (suc n) rw =
  Pair.productRepresented gi u v w (groupPower gi w n) rw
    (powerRepresented gi u v w n rw)

transportRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) {x y : G} →
  x ≡ y →
  Pair.RepresentedByPair gi u v x →
  Pair.RepresentedByPair gi u v y
transportRepresented gi u v refl rx = rx

record JMDStepsTwoToFour
  {G : Set} (gi : TM.GroupWithInverse G) (u v : G) : Set where
  field
    w x4 beta : G
    wIsProduct : w ≡ Pair.multiply gi x4 beta
    wFromPair : Pair.RepresentedByPair gi u v w
    x4IsFifthPower : x4 ≡ groupPower gi w 5
    betaIsSixthPower : beta ≡ groupPower gi w 6

open JMDStepsTwoToFour public

-- The cited w = x4 beta identity and cyclic scope are source semantics;
-- these proofs use only the two power equalities and the actual w word.

traceStepThreeX4 :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) →
  (trace : JMDStepsTwoToFour gi u v) →
  Pair.RepresentedByPair gi u v (x4 trace)
traceStepThreeX4 gi u v trace =
  transportRepresented gi u v (sym (x4IsFifthPower trace))
    (powerRepresented gi u v (w trace) 5 (wFromPair trace))

traceStepFourBeta :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) →
  (trace : JMDStepsTwoToFour gi u v) →
  Pair.RepresentedByPair gi u v (beta trace)
traceStepFourBeta gi u v trace =
  transportRepresented gi u v (sym (betaIsSixthPower trace))
    (powerRepresented gi u v (w trace) 6 (wFromPair trace))

traceStepsThreeAndFour :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) →
  (trace : JMDStepsTwoToFour gi u v) →
  Pair._∧_
    (Pair.RepresentedByPair gi u v (x4 trace))
    (Pair.RepresentedByPair gi u v (beta trace))
traceStepsThreeAndFour gi u v trace =
  Pair._,,_
    (traceStepThreeX4 gi u v trace)
    (traceStepFourBeta gi u v trace)
