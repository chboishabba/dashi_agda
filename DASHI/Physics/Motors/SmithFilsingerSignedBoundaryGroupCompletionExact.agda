module DASHI.Physics.Motors.SmithFilsingerSignedBoundaryGroupCompletionExact where

-- F15 maximum cut: signed work WITHOUT assuming that environmental
-- incident >= environmental outgoing. A pair of nonnegative quantities
-- denotes a signed real-work balance by its cross-sum equivalence.
--
-- No actual ambient source work or original-device history is inferred.
-- Reuses exactly the original signed MidpointTwoPortWorkWindow boundary
-- and the repo Nat order/cancellation owners. This complements the
-- earlier positive-net-source cap; reverse net flow remains representable.
--
-- Attribution: user-origin Smith/Filsinger nonlinear differential
-- source/sink hypothesis; original MidpointTwoPortWorkExact signed ledger.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Group-completion carrier. We assert only the exact properties proved
-- below, not the stronger claim that a quotient/group was constructed.
record DirectedSignedWork : Set where
  constructor directedSignedWork
  field
    incoming outgoing : Nat

-- Equality of SIGNED work is cross-multiplied equality, not identity
-- of arbitrarily selected (incoming,outgoing) representative pairs.
-- Signed-work equivalence, used in types, avoids treating two pairs of
-- equal net work as literally equal record values.
sameSignedWork : DirectedSignedWork → DirectedSignedWork → Set
sameSignedWork a b =
  DirectedSignedWork.incoming a + DirectedSignedWork.outgoing b
    ≡ DirectedSignedWork.incoming b + DirectedSignedWork.outgoing a


-- The cross-sum relation is an exact equivalence on pairs of Nat.
-- There is NO quotient type claimed here; different pairs may represent
-- the same signed work. Cancellation makes the relation transitive.
sameSignedReflexive : (a : DirectedSignedWork) → sameSignedWork a a
sameSignedReflexive a = refl

sameSignedSymmetric :
  (a b : DirectedSignedWork) →
  sameSignedWork a b → sameSignedWork b a
sameSignedSymmetric a b equal = Bound.sym equal

sameSignedTransitive :
  (a b c : DirectedSignedWork) →
  sameSignedWork a b →
  sameSignedWork b c →
  sameSignedWork a c
sameSignedTransitive a b c ab bc =
  Cycle.+-cancelRight _ _ (B + bOut)
    (Cycle.trans
      (solve 6
        (λ A aa B bb C cc →
          ((A :+ cc) :+ (B :+ bb))
            := ((A :+ bb) :+ (B :+ cc)))
        refl A aOut B bOut C cOut)
      (Cycle.trans
        (Cycle.cong (λ x → x + (B + cOut)) ab)
        (Cycle.trans
          (Cycle.cong (λ x → (B + aOut) + x) bc)
          (solve 6
            (λ A aa B bb C cc →
              ((B :+ aa) :+ (C :+ bb))
                := ((C :+ aa) :+ (B :+ bb)))
            refl A aOut B bOut C cOut))))
  where
    A : Nat
    A = DirectedSignedWork.incoming a
    aOut : Nat
    aOut = DirectedSignedWork.outgoing a
    B : Nat
    B = DirectedSignedWork.incoming b
    bOut : Nat
    bOut = DirectedSignedWork.outgoing b
    C : Nat
    C = DirectedSignedWork.incoming c
    cOut : Nat
    cOut = DirectedSignedWork.outgoing c


-- Exact quantisation obstruction: one integer energy quantum has NO
-- two equal signed-Nat-pair halves. A nontrivial universal lossless
-- rational/real-field -> integer-meter additive map must not be assumed.
--
-- This is an original mathematical negative control on quantisation,
-- NOT a claim about real meter resolution or laboratory power.
doubleNat : Nat → Nat
doubleNat zero = zero
doubleNat (suc n) = suc (suc (doubleNat n))

doubleNatNormalization : (n : Nat) → n + n ≡ doubleNat n
doubleNatNormalization zero = refl
doubleNatNormalization (suc n)
  rewrite Cycle.+-sucRight n n
        | doubleNatNormalization n = refl

doubleCannotBeOdd :
  (a b : Nat) → doubleNat a ≡ suc (doubleNat b) → Port.Contradiction
doubleCannotBeOdd zero zero ()
doubleCannotBeOdd zero (suc b) ()
doubleCannotBeOdd (suc a) zero ()
doubleCannotBeOdd (suc a) (suc b) eq =
  doubleCannotBeOdd a b
    (Cycle.sucInjective (Cycle.sucInjective eq))

-- Signed work equality is the CROSS-SUM relation, not literal equality
-- of Nat pairs. The contradiction works for ANY putative half-work pair.
oneWorkQuantumHasNoExactSignedHalf :
  (a b : Nat) →
  sameSignedWork
    (combinedPorts (directedSignedWork a b) (directedSignedWork a b))
    (directedSignedWork (suc zero) zero) →
  Port.Contradiction
oneWorkQuantumHasNoExactSignedHalf a b claimed =
  doubleCannotBeOdd a b
    (Cycle.trans
      (Bound.sym (doubleNatNormalization a))
      (Cycle.trans
        (Bound.sym (Cycle.+-zeroRight (a + a)))
        (Cycle.trans claimed
          (Cycle.cong suc (doubleNatNormalization b)))))

netNaturalPort : Port.MidpointTwoPortWorkWindow → DirectedSignedWork
netNaturalPort p =
  directedSignedWork
    (Port.MidpointTwoPortWorkWindow.naturalIncident p)
    (Port.MidpointTwoPortWorkWindow.naturalOutgoing p)

netControllerPort : Port.MidpointTwoPortWorkWindow → DirectedSignedWork
netControllerPort p =
  directedSignedWork
    (Port.MidpointTwoPortWorkWindow.controllerIncident p)
    (Port.MidpointTwoPortWorkWindow.controllerOutgoing p)

combinedPorts : DirectedSignedWork → DirectedSignedWork → DirectedSignedWork
combinedPorts a b =
  directedSignedWork
    (DirectedSignedWork.incoming a + DirectedSignedWork.incoming b)
    (DirectedSignedWork.outgoing a + DirectedSignedWork.outgoing b)


-- Additive inverse is a SWAP of directed natural-work streams,
-- never an invalid Nat subtraction. The following is equivalence in
-- cross-sum work, not literal equality of record representatives.
negativeSignedWork : DirectedSignedWork → DirectedSignedWork
negativeSignedWork a =
  directedSignedWork
    (DirectedSignedWork.outgoing a)
    (DirectedSignedWork.incoming a)

signedWorkZero : DirectedSignedWork
signedWorkZero = directedSignedWork zero zero

signedWorkInverseCancels :
  (a : DirectedSignedWork) →
  sameSignedWork (combinedPorts a (negativeSignedWork a)) signedWorkZero
signedWorkInverseCancels a =
  solve 2
    (λ x y →
      ((x :+ y) :+ con 0) := (con 0 :+ (y :+ x)))
    refl (DirectedSignedWork.incoming a)
         (DirectedSignedWork.outgoing a)

sameSignedAddCongruenceRight :
  (a b c : DirectedSignedWork) →
  sameSignedWork a b →
  sameSignedWork (combinedPorts a c) (combinedPorts b c)
sameSignedAddCongruenceRight a b c ab =
  Cycle.trans
    (solve 4
      (λ ai ao bi bo →
        ((ai :+ ci) :+ (bo :+ co))
          := ((ai :+ bo) :+ (ci :+ co)))
      refl ai ao bi bo)
    (Cycle.trans
      (Cycle.cong (λ z → z + (ci + co)) ab)
      (solve 4
        (λ ai ao bi bo →
          ((bi :+ ao) :+ (ci :+ co))
            := ((bi :+ ci) :+ (ao :+ co)))
        refl ai ao bi bo))
  where
    ai : Nat
    ai = DirectedSignedWork.incoming a
    ao : Nat
    ao = DirectedSignedWork.outgoing a
    bi : Nat
    bi = DirectedSignedWork.incoming b
    bo : Nat
    bo = DirectedSignedWork.outgoing b
    ci : Nat
    ci = DirectedSignedWork.incoming c
    co : Nat
    co = DirectedSignedWork.outgoing c

paidLoadAndLoss : Port.MidpointTwoPortWorkWindow → DirectedSignedWork
paidLoadAndLoss p =
  directedSignedWork
    (Port.MidpointTwoPortWorkWindow.usefulWork p
      + Port.MidpointTwoPortWorkWindow.internalLoss p)
    zero

-- Exact source-independent algebra: both natural and powered ports may
-- have net reversed flow; still the signed external power equals useful
-- work + dissipation after every relevant store returns.
signedRawPortBalance :
  (ni ci no co initial final load loss : Nat) →
  initial ≡ final →
  (ni + ci) + initial
    ≡ load + (loss + (no + (co + final))) →
  (ni + ci) + zero ≡ (load + loss) + (no + co)
signedRawPortBalance ni ci no co initial final load loss
  restored originalBalance =
  Cycle.trans
    (Bound.sym (Cycle.+-zeroRight (ni + ci)))
    (Cycle.+-cancelRight _ _ final
      (Cycle.trans
        (Bound.sym
          (Cycle.cong (λ z → (ni + ci) + z) restored))
        (Cycle.trans
          originalBalance
          (solve 5
            (λ l h n c s →
              (l :+ (h :+ (n :+ (c :+ s))))
                := (((l :+ h) :+ (n :+ c)) :+ s))
            refl load loss no co final))))

-- Direct theorem over the canonical two-port ledger. No Nat subtraction
-- and no nonnegative-natural-net premise is imposed.
originalTwoPortSignedWorkConservation :
  (p : Port.MidpointTwoPortWorkWindow) →
  Port.MidpointTwoPortWorkWindow.initialStored p
    ≡ Port.MidpointTwoPortWorkWindow.finalStored p →
  sameSignedWork
    (combinedPorts (netNaturalPort p) (netControllerPort p))
    (paidLoadAndLoss p)
originalTwoPortSignedWorkConservation p restored =
  signedRawPortBalance
    (Port.MidpointTwoPortWorkWindow.naturalIncident p)
    (Port.MidpointTwoPortWorkWindow.controllerIncident p)
    (Port.MidpointTwoPortWorkWindow.naturalOutgoing p)
    (Port.MidpointTwoPortWorkWindow.controllerOutgoing p)
    (Port.MidpointTwoPortWorkWindow.initialStored p)
    (Port.MidpointTwoPortWorkWindow.finalStored p)
    (Port.MidpointTwoPortWorkWindow.usefulWork p)
    (Port.MidpointTwoPortWorkWindow.internalLoss p)
    restored
    (Port.MidpointTwoPortWorkWindow.completeBoundaryBalance p)

-- A negative-NET environmental port is legitimate (net environmental
-- SINK), but cannot become free receiver output. If more environmental
-- work leaves than enters and the powered controller has nonnegative
-- net work, the controller must ALSO pay for this return flow.
--
-- Derivation uses only same-original boundary conservation and restore.
reverseEnvironmentalFlowConsumesControllerWork :
  (p : Port.MidpointTwoPortWorkWindow)
  (reverseToEnvironment controllerNet : Nat) →
  Port.MidpointTwoPortWorkWindow.naturalOutgoing p
    ≡ Port.MidpointTwoPortWorkWindow.naturalIncident p
       + reverseToEnvironment →
  Port.MidpointTwoPortWorkWindow.controllerIncident p
    ≡ Port.MidpointTwoPortWorkWindow.controllerOutgoing p
       + controllerNet →
  Port.MidpointTwoPortWorkWindow.initialStored p
    ≡ Port.MidpointTwoPortWorkWindow.finalStored p →
  controllerNet ≡
    (Port.MidpointTwoPortWorkWindow.usefulWork p
      + Port.MidpointTwoPortWorkWindow.internalLoss p)
      + reverseToEnvironment
reverseEnvironmentalFlowConsumesControllerWork p reversed controllerNet
  netReverse netController restored =
  Cycle.+-cancelLeft
    (ni + co) controllerNet ((load + loss) + reversed)
    (Cycle.trans
      (solve 3
        (λ ni co ctl →
          ((ni :+ co) :+ ctl)
            := (ni :+ (co :+ ctl)))
        refl ni co controllerNet)
      (Cycle.trans
        (Cycle.cong (λ z → ni + z) (Bound.sym netController))
        (Cycle.trans
          (rawBalanceAfterReturn p restored)
          (Cycle.trans
            (Cycle.cong
              (λ z → (load + loss) + (z + co))
              netReverse)
            (solve 5
              (λ ni co h k rv →
                ((h :+ k) :+ ((ni :+ rv) :+ co))
                  := ((ni :+ co) :+ ((h :+ k) :+ rv)))
              refl ni co load loss reversed)))))
  where
    ni : Nat
    ni = Port.MidpointTwoPortWorkWindow.naturalIncident p
    co : Nat
    co = Port.MidpointTwoPortWorkWindow.controllerOutgoing p
    load : Nat
    load = Port.MidpointTwoPortWorkWindow.usefulWork p
    loss : Nat
    loss = Port.MidpointTwoPortWorkWindow.internalLoss p

    rawBalanceAfterReturn :
      (x : Port.MidpointTwoPortWorkWindow) →
      Port.MidpointTwoPortWorkWindow.initialStored x
        ≡ Port.MidpointTwoPortWorkWindow.finalStored x →
      Port.MidpointTwoPortWorkWindow.naturalIncident x
        + Port.MidpointTwoPortWorkWindow.controllerIncident x
      ≡ (Port.MidpointTwoPortWorkWindow.usefulWork x
        + Port.MidpointTwoPortWorkWindow.internalLoss x)
        + (Port.MidpointTwoPortWorkWindow.naturalOutgoing x
          + Port.MidpointTwoPortWorkWindow.controllerOutgoing x)
    rawBalanceAfterReturn x store =
      Cycle.trans
        (Bound.sym (Cycle.+-zeroRight _))
        (originalTwoPortSignedWorkConservation x store)


-- Sharp reverse-source negative control: environmental sink work is
-- controller-paid and cannot be counted as additional useful load.
-- Even when the natural port reverses sign, the bound is exact.
reverseEnvironmentalLoadPlusSinkBelowController :
  (p : Port.MidpointTwoPortWorkWindow)
  (reversed controllerNet : Nat) →
  Port.MidpointTwoPortWorkWindow.naturalOutgoing p
    ≡ Port.MidpointTwoPortWorkWindow.naturalIncident p + reversed →
  Port.MidpointTwoPortWorkWindow.controllerIncident p
    ≡ Port.MidpointTwoPortWorkWindow.controllerOutgoing p + controllerNet →
  Port.MidpointTwoPortWorkWindow.initialStored p
    ≡ Port.MidpointTwoPortWorkWindow.finalStored p →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork p + reversed)
    controllerNet
reverseEnvironmentalLoadPlusSinkBelowController
  p reversed ctrl reverseWork controllerWork storeReturns =
  Bound.transportUpper
    (Cycle.trans
      (solve 3
        (λ load loss sink →
          ((load :+ sink) :+ loss)
            := ((load :+ loss) :+ sink))
        refl useful losses reversed)
      (Bound.sym
        (reverseEnvironmentalFlowConsumesControllerWork
          p reversed ctrl reverseWork controllerWork storeReturns)))
    (Bound.≤-append (useful + reversed) losses)
  where
    useful : Nat
    useful = Port.MidpointTwoPortWorkWindow.usefulWork p
    losses : Nat
    losses = Port.MidpointTwoPortWorkWindow.internalLoss p

-- Same selected original source b/f: unlike the previously formalised
-- nonnegative-natural-net source cap, this proof requires NO such
-- admission and remains valid for a negative net environmental port.
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld

originalReverseEnvironmentalPortFundedByController :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (environmentalReturn controllerNet : Nat) →
  Port.MidpointTwoPortWorkWindow.naturalOutgoing
    (Weld.FormalFieldToPort.portWindow f)
    ≡ Port.MidpointTwoPortWorkWindow.naturalIncident
      (Weld.FormalFieldToPort.portWindow f) + environmentalReturn →
  Port.MidpointTwoPortWorkWindow.controllerIncident
    (Weld.FormalFieldToPort.portWindow f)
    ≡ Port.MidpointTwoPortWorkWindow.controllerOutgoing
      (Weld.FormalFieldToPort.portWindow f) + controllerNet →
  Port.MidpointTwoPortWorkWindow.initialStored
    (Weld.FormalFieldToPort.portWindow f)
    ≡ Port.MidpointTwoPortWorkWindow.finalStored
      (Weld.FormalFieldToPort.portWindow f) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f) + environmentalReturn)
    controllerNet
originalReverseEnvironmentalPortFundedByController b f environmentalReturn
  controllerNet reverseLaw controllerLaw restored =
  reverseEnvironmentalLoadPlusSinkBelowController
    (Weld.FormalFieldToPort.portWindow f)
    environmentalReturn controllerNet reverseLaw controllerLaw restored


-- Existing canonical negative control re-used UNCHANGED, not a new
-- source-current simulation or original-device observation. The owner
-- exhibits environmental net *outflow* under a driven controller.
-- In that actual finite record, controller net 2 pays load 1 and
-- returned environmental work 1, with all storage restored.
originalDriverOnlyReverseFlowIsPaid :
  2 ≡
    (Port.MidpointTwoPortWorkWindow.usefulWork
      Port.driverOnlyCanRadiateIntoEnvironment
      + Port.MidpointTwoPortWorkWindow.internalLoss
        Port.driverOnlyCanRadiateIntoEnvironment)
      + 1
originalDriverOnlyReverseFlowIsPaid =
  reverseEnvironmentalFlowConsumesControllerWork
    Port.driverOnlyCanRadiateIntoEnvironment 1 2 refl refl refl

originalDriverOnlySinkBound :
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      Port.driverOnlyCanRadiateIntoEnvironment + 1) 2
originalDriverOnlySinkBound =
  reverseEnvironmentalLoadPlusSinkBelowController
    Port.driverOnlyCanRadiateIntoEnvironment 1 2 refl refl refl
