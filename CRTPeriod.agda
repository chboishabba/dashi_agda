module CRTPeriod where

open import Agda.Builtin.Nat      using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import Data.Nat.Base   using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_; [m+kn]%n≡m%n)
open import Data.Nat.Properties as NatP using (*-assoc; *-comm; +-assoc)

------------------------------------------------------------------------
-- Repo-defined digit function:

d : Nat → Nat
d N = ((N % 71) + (N % 59) + (N % 47)) % 10

period : Nat
period = 71 * 59 * 47  -- 196883

------------------------------------------------------------------------
-- The theorem statement (R1):
-- d(N + k*period) = d(N) for all k.
--
-- Proof is standard modular arithmetic:
-- (N + k*period) mod p = N mod p for p ∈ {71,59,47}
-- then propagate through sum and mod 10.
--
-- You can discharge this using stdlib DivMod lemmas, or (DASHI-style)
-- by importing a small proof certificate.

instance
  nonZero71 : NonZero 71
  nonZero71 = nonZero
  nonZero59 : NonZero 59
  nonZero59 = nonZero
  nonZero47 : NonZero 47
  nonZero47 = nonZero
  nonZero10 : NonZero 10
  nonZero10 = nonZero

period-thm : ∀ N k → d (N + k * period) ≡ d N
period-thm N k =
  period-thm' step71 step59 step47
  where
    k71 = k * (59 * 47)
    k59 = k * (71 * 47)
    k47 = k * (71 * 59)

    period≡59·47·71 : period ≡ (59 * 47) * 71
    period≡59·47·71 =
      trans (NatP.*-assoc 71 59 47)
        (NatP.*-comm 71 (59 * 47))

    period≡71·47·59 : period ≡ (71 * 47) * 59
    period≡71·47·59 =
      trans (NatP.*-assoc 71 59 47)
        (trans (cong (λ x → 71 * x) (NatP.*-comm 59 47))
          (sym (NatP.*-assoc 71 47 59)))

    period≡71·59·47 : period ≡ (71 * 59) * 47
    period≡71·59·47 = NatP.*-assoc 71 59 47

    eq71 : k * period ≡ k71 * 71
    eq71 = trans (cong (λ x → k * x) period≡59·47·71) (sym (NatP.*-assoc k (59 * 47) 71))

    eq59 : k * period ≡ k59 * 59
    eq59 = trans (cong (λ x → k * x) period≡71·47·59) (sym (NatP.*-assoc k (71 * 47) 59))

    eq47 : k * period ≡ k47 * 47
    eq47 = trans (cong (λ x → k * x) period≡71·59·47) (sym (NatP.*-assoc k (71 * 59) 47))

    step71 : (N + k * period) % 71 ≡ N % 71
    step71 = trans (cong (λ v → (N + v) % 71) eq71) ([m+kn]%n≡m%n N k71 71)

    step59 : (N + k * period) % 59 ≡ N % 59
    step59 = trans (cong (λ v → (N + v) % 59) eq59) ([m+kn]%n≡m%n N k59 59)

    step47 : (N + k * period) % 47 ≡ N % 47
    step47 = trans (cong (λ v → (N + v) % 47) eq47) ([m+kn]%n≡m%n N k47 47)

    period-thm' :
      (s71 : (N + k * period) % 71 ≡ N % 71) →
      (s59 : (N + k * period) % 59 ≡ N % 59) →
      (s47 : (N + k * period) % 47 ≡ N % 47) →
      d (N + k * period) ≡ d N
    period-thm' s71 s59 s47 rewrite s71 | s59 | s47 = refl
