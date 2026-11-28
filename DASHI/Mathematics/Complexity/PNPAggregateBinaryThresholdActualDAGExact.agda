module DASHI.Mathematics.Complexity.PNPAggregateBinaryThresholdActualDAGExact where

-- Native binary prefix clock on the ORIGINAL aggregate threshold DAG.
-- Read bits most-significant first. The state never exceeds excessBound.
-- Classical binary saturation; DASHI attachment to original count/encode/decode.
-- No unrestricted semantic coverage or complexity separation is inferred.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_)
open import Data.Vec.Base using (Vec)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import DASHI.Mathematics.Complexity.PNPAggregateGateCountExact as G
import DASHI.Mathematics.Complexity.PNPAggregateThresholdArithmeticExact as A
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T
import DASHI.Mathematics.Complexity.PNPAggregateHardCNFWeldExact as H
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as F

bit : Bool → Nat
bit false = zero
bit true = suc zero

step : Nat → Bool → Nat
step x b = (x + x) + bit b

minOfLeft≤ : ∀ {x m} → x ≤ m → A.mn x m ≡ x
minOfLeft≤ {m = zero} z≤n = refl
minOfLeft≤ {m = suc m} z≤n = refl
minOfLeft≤ (s≤s h) = cong suc (minOfLeft≤ h)

minOfRight≤ : ∀ {x m} → m ≤ x → A.mn x m ≡ m
minOfRight≤ z≤n = refl
minOfRight≤ (s≤s h) = cong suc (minOfRight≤ h)

stepExtensive : ∀ x b → x ≤ step x b
stepExtensive x b =
  N.≤-trans (N.m≤m+n x x) (N.m≤m+n (x + x) (bit b))

stepClamp : ∀ x m b →
  A.mn (step (A.mn x m) b) m ≡ A.mn (step x b) m
stepClamp x m b with N.≤-total x m
... | inj₁ h rewrite minOfLeft≤ h = refl
... | inj₂ h rewrite minOfRight≤ h
  | minOfRight≤ (stepExtensive m b)
  | minOfRight≤ (N.≤-trans h (stepExtensive x b)) = refl

valueFrom : Nat → List Bool → Nat
valueFrom x [] = x
valueFrom x (b ∷ bs) = valueFrom (step x b) bs

satFrom : Nat → Nat → List Bool → Nat
satFrom m x [] = x
satFrom m x (b ∷ bs) = satFrom m (A.mn (step x b) m) bs

satInvariant : ∀ m x bs →
  satFrom m (A.mn x m) bs ≡ A.mn (valueFrom x bs) m
satInvariant m x [] = refl
satInvariant m x (b ∷ bs)
  rewrite stepClamp x m b = satInvariant m (step x b) bs

binaryValue : List Bool → Nat
binaryValue = valueFrom zero

saturatedBits : List Bool → Nat → Nat
saturatedBits bs m = satFrom m zero bs

saturatedValue : ∀ bs m →
  saturatedBits bs m ≡ A.mn (binaryValue bs) m
saturatedValue bs zero = satInvariant zero zero bs
saturatedValue bs (suc m) = satInvariant (suc m) zero bs

satStateBound : ∀ m x bs → x ≤ m → satFrom m x bs ≤ m
satStateBound m x [] hx = hx
satStateBound m x (b ∷ bs) hx =
  satStateBound m (A.mn (step x b) m) bs (G.minRight (step x b) m)

saturatedBound : ∀ bs m → saturatedBits bs m ≤ m
saturatedBound bs m = satStateBound m zero bs z≤n

binaryCircuit : ∀ {n} → T.Rows n → List Bool → C.ConcreteBooleanCircuit n
binaryCircuit rs bs = T.aggregateCircuit rs (saturatedBits bs (G.excessBound rs))

binaryCircuitIsOriginal : ∀ {n} (rs : T.Rows n) bs →
  binaryCircuit rs bs ≡ G.boundedCircuit rs (binaryValue bs)
binaryCircuitIsOriginal rs bs = cong (T.aggregateCircuit rs)
  (saturatedValue bs (G.excessBound rs))

binaryGateCount : ∀ {n} (rs : T.Rows n) bs →
  C.gateCount (binaryCircuit rs bs) ≡
    suc (suc (G.tableCost (G.excessBound rs)
      (suc (saturatedBits bs (G.excessBound rs))) + (G.rowCost rs + zero)))
binaryGateCount rs bs = G.gateCountExact rs (saturatedBits bs (G.excessBound rs))

binaryDemandCNF : ∀ {n} (rs : T.Rows n) bs → CNF.CNF n →
  CNF.CNF (n + C.gateCount (binaryCircuit rs bs))
binaryDemandCNF rs bs hard = H.DemandCNF rs
  (saturatedBits bs (G.excessBound rs)) hard

binaryDecode : ∀ {n} (rs : T.Rows n) bs (hard : CNF.CNF n)
  (bits : CNF.Bits (n + C.gateCount (binaryCircuit rs bs))) →
  CNF.evaluateCNF (binaryDemandCNF rs bs hard) bits ≡ true →
  (H.hardValue hard (F.inputVectorFromGlobal bits) ≡ true) ×
  (A.potential rs (F.inputVectorFromGlobal bits) ≤ binaryValue bs)
binaryDecode rs bs hard bits yes with
  H.decodeDemand rs (saturatedBits bs (G.excessBound rs)) hard bits yes
... | hd , cap = hd , G.clampSound rs (binaryValue bs) _
  (subst (λ k → A.potential rs (F.inputVectorFromGlobal bits) ≤ k)
    (saturatedValue bs (G.excessBound rs)) cap)

binaryEncode : ∀ {n} (rs : T.Rows n) bs (hard : CNF.CNF n)
  (x : Vec Bool n) → H.hardValue hard x ≡ true →
  A.potential rs x ≤ binaryValue bs →
  CNF.evaluateCNF (binaryDemandCNF rs bs hard)
    (H.canonicalBits rs (saturatedBits bs (G.excessBound rs)) x) ≡ true
binaryEncode rs bs hard x hd cap =
  H.encodeDemand rs (saturatedBits bs (G.excessBound rs)) hard x hd
    (subst (λ k → A.potential rs x ≤ k)
      (sym (saturatedValue bs (G.excessBound rs)))
      (G.clampComplete rs (binaryValue bs) x cap))
