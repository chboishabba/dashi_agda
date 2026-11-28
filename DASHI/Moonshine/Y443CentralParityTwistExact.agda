module DASHI.Moonshine.Y443CentralParityTwistExact where

-- Ivanov/Bray Y443 original presentation, JMD source words.
-- The actual Bimonster subgroup has an odd central involution.
-- DASHI: exact central twist on its selected subgroup (not all
-- Bimonster elements), with original-word parity from the existing owner.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Alg
import DASHI.Moonshine.Y443Mod2OddEdgeCentralCharacterExact as Par
import DASHI.Moonshine.TwistedModuleModularity as TM

module Selected
  {G : Set}
  (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (c : G)
  (central : (x : G) → Pair.multiply gi c x ≡ Pair.multiply gi x c)
  (square : Pair.multiply gi c c ≡ Pair.identity gi)
  where

  open Alg using (sym; trans; cong; cong₂)
  module P = Alg.PowerAlgebra gi
  open P using (e; mul; assoc; leftId; rightId)

  phase : Bool → G
  phase false = e
  phase true = c

  phaseProduct : (p q : Bool) →
    mul (phase p) (phase q) ≡ phase (Par._⊕_ p q)
  phaseProduct false q = leftId (phase q)
  phaseProduct true false = rightId c
  phaseProduct true true = square

  twistedNodes : Y.Node → G
  twistedNodes n = mul (nodes n) c

  charge : Y.Node → Bool
  charge _ = true

  reorder : (x y z : G) →
    mul (mul x c) (mul y z) ≡ mul (mul x y) (mul c z)
  reorder x y z =
    trans (assoc x c (mul y z))
      (trans (cong (mul x) (sym (assoc c y z)))
        (trans (cong (λ t → mul x (mul t z)) (central y))
          (trans (cong (mul x) (assoc y c z))
            (sym (assoc x y (mul c z))))))

  twistWord : (w : Y.Word) →
    Pair.evaluateCoxeterWord gi twistedNodes w ≡
    mul (Pair.evaluateCoxeterWord gi nodes w) (phase (Par.parityWord charge w))
  twistWord [] = sym (leftId e)
  twistWord (n ∷ w) =
    trans (cong (mul (mul (nodes n) c)) (twistWord w))
      (trans (reorder (nodes n) (Pair.evaluateCoxeterWord gi nodes w)
                (phase (Par.parityWord charge w)))
        (cong (mul (mul (nodes n) (Pair.evaluateCoxeterWord gi nodes w)))
          (phaseProduct true (Par.parityWord charge w))))

  evenRelationPreserved : (w : Y.Word) →
    Par.parityWord charge w ≡ false →
    Pair.evaluateCoxeterWord gi nodes w ≡ e →
    Pair.evaluateCoxeterWord gi twistedNodes w ≡ e
  evenRelationPreserved w p r =
    trans (twistWord w)
      (trans (cong₂ mul r (cong phase p)) (leftId e))

  originalCentralIsOdd :
    Par.parityWord charge Y.centralInvolutionRelator ≡ true
  originalCentralIsOdd = refl

  centralRemoved :
    Pair.evaluateCoxeterWord gi nodes Y.centralInvolutionRelator ≡ c →
    Pair.evaluateCoxeterWord gi twistedNodes Y.centralInvolutionRelator ≡ e
  centralRemoved r =
    trans (twistWord Y.centralInvolutionRelator)
      (trans (cong₂ mul r (cong phase originalCentralIsOdd)) square)

-- For the 79 other actual words, source parity is even. The runtime
-- adapter checks all 80 in each factor. This lemma does not assume or
-- construct the original selected characteristic-zero FLM VOA.
