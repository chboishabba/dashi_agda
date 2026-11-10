module DASHI.Biology.BH4PNPOrderedEnergyHistoryExact where

-- P0.06 reusable ordered-additive energy ledger.
-- Unlike the Nat accounting owner, the energy carrier is abstract:
-- it may later be instantiated by genuine real-valued free energies.
-- No ordered-real instance or original Rhea physical source is
-- manufactured here; those remain independent source/proof obligations.
--
-- Source attribution: elementary ordered commutative-monoid algebra,
-- implemented as assistance for the original DASHI BH4/369 programme.

open import DASHI.Core.Prelude

record OrderedEnergyCarrier : Set₁ where
  field
    Energy : Set
    zeroEnergy : Energy
    _⊕_ : Energy → Energy → Energy
    _⊑_ : Energy → Energy → Set

    energyAssoc : (a b c : Energy) →
      (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    energyComm : (a b : Energy) → a ⊕ b ≡ b ⊕ a
    energyRightUnit : (a : Energy) → a ⊕ zeroEnergy ≡ a

    orderTransitive : {a b c : Energy} →
      a ⊑ b → b ⊑ c → a ⊑ c
    orderLeftMonotone : (a : Energy) {b c : Energy} →
      b ⊑ c → (a ⊕ b) ⊑ (a ⊕ c)
    nonnegativeSum : {a b : Energy} →
      zeroEnergy ⊑ a → zeroEnergy ⊑ b →
      zeroEnergy ⊑ (a ⊕ b)

module EnergyLaws (O : OrderedEnergyCarrier) where
  open OrderedEnergyCarrier O

  shuffleRight : (a b c : Energy) →
    a ⊕ (b ⊕ c) ≡ (a ⊕ c) ⊕ b
  shuffleRight a b c =
    trans (cong (λ x → a ⊕ x) (energyComm b c))
          (sym (energyAssoc a c b))

  shuffleAdjacent : (a b c : Energy) →
    (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
  shuffleAdjacent a b c =
    trans (energyAssoc a b c) (shuffleRight a b c)

  record EnergyStep (initial final : Energy) : Set where
    constructor energyStep
    field
      loss credit : Energy
      lossNonnegative : zeroEnergy ⊑ loss
      exactLedger : final ⊕ loss ≡ initial ⊕ credit
  open EnergyStep public

  compose : {initial middle final : Energy} →
    EnergyStep initial middle →
    EnergyStep middle final →
    EnergyStep initial final
  compose {initial} {middle} {final} first second =
    energyStep
      (loss first ⊕ loss second)
      (credit first ⊕ credit second)
      (nonnegativeSum (lossNonnegative first) (lossNonnegative second))
      (trans
        (shuffleRight final (loss first) (loss second))
        (trans
          (cong (λ x → x ⊕ loss first) (exactLedger second))
          (trans
            (shuffleAdjacent middle (credit second) (loss first))
            (trans
              (cong (λ x → x ⊕ credit second) (exactLedger first))
              (energyAssoc initial (credit first) (credit second))))))

  data EnergyHistory : Energy → Energy → Set where
    one : {initial final : Energy} →
      EnergyStep initial final → EnergyHistory initial final
    follow : {initial middle final : Energy} →
      EnergyStep initial middle →
      EnergyHistory middle final →
      EnergyHistory initial final

  historyLedger : {initial final : Energy} →
    EnergyHistory initial final → EnergyStep initial final
  historyLedger (one s) = s
  historyLedger (follow s rest) =
    compose s (historyLedger rest)

  -- No cancellation by subtraction: the conclusion follows solely
  -- from nonnegative loss, additive monotonicity and exact equality.
  oneStepUpperBound : {initial final : Energy} →
    (s : EnergyStep initial final) →
    final ⊑ (initial ⊕ credit s)
  oneStepUpperBound {initial} {final} s =
    subst (λ x → final ⊑ x)
      (exactLedger s)
      (subst (λ x → x ⊑ (final ⊕ loss s))
        (energyRightUnit final)
        (orderLeftMonotone final (lossNonnegative s)))

  historyUpperBound : {initial final : Energy} →
    (history : EnergyHistory initial final) →
    final ⊑ (initial ⊕ credit (historyLedger history))
  historyUpperBound history = oneStepUpperBound (historyLedger history)

  zeroCreditHistoryNonincreasing : {initial final : Energy} →
    (history : EnergyHistory initial final) →
    credit (historyLedger history) ≡ zeroEnergy →
    final ⊑ initial
  zeroCreditHistoryNonincreasing {initial} {final} history creditZero =
    subst (λ x → final ⊑ x)
      (trans
        (cong (λ x → initial ⊕ x) creditZero)
        (energyRightUnit initial))
      (historyUpperBound history)
