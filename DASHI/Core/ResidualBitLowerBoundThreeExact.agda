module DASHI.Core.ResidualBitLowerBoundThreeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- EXACT BIT LOWER BOUND FOR A THREE-STATE FIBRE
--
-- This is the first literal ceil(log2 k) instance: k = 3 future/fine classes
-- inside one coarse fibre cannot be encoded by one Boolean residual, while two
-- Boolean coordinates suffice.
------------------------------------------------------------------------

data Fine : Set where
  first second third : Fine

data Coarse : Set where
  commonClass : Coarse

coarsen : Fine → Coarse
coarsen state = commonClass

pairwiseDistinct12 : first ≡ second → ⊥
pairwiseDistinct12 ()

pairwiseDistinct13 : first ≡ third → ⊥
pairwiseDistinct13 ()

pairwiseDistinct23 : second ≡ third → ⊥
pairwiseDistinct23 ()

------------------------------------------------------------------------
-- Pigeonhole for three states into one bit.
------------------------------------------------------------------------

threeBooleansHaveCollision :
  (a b c : Bool) →
  (a ≡ b) ⊎ ((a ≡ c) ⊎ (b ≡ c))
threeBooleansHaveCollision false false c = inj₁ refl
threeBooleansHaveCollision false true false = inj₂ (inj₁ refl)
threeBooleansHaveCollision false true true = inj₂ (inj₂ refl)
threeBooleansHaveCollision true false false = inj₂ (inj₂ refl)
threeBooleansHaveCollision true false true = inj₂ (inj₁ refl)
threeBooleansHaveCollision true true c = inj₁ refl

record OneBitExactReopening (residual : Fine → Bool) : Set₁ where
  constructor oneBitExactReopening
  field
    reopen : Coarse → Bool → Fine
    reopenExact : (state : Fine) → reopen (coarsen state) (residual state) ≡ state

open OneBitExactReopening public

oneBitCannotExactlyReopenThreeStateFibre :
  (residual : Fine → Bool) →
  OneBitExactReopening residual → ⊥
oneBitCannotExactlyReopenThreeStateFibre residual receipt
  with threeBooleansHaveCollision (residual first) (residual second) (residual third)
... | inj₁ firstSecondEqual =
  pairwiseDistinct12
    (trans
      (sym (reopenExact receipt first))
      (trans
        (cong (reopen receipt commonClass) firstSecondEqual)
        (reopenExact receipt second)))
... | inj₂ (inj₁ firstThirdEqual) =
  pairwiseDistinct13
    (trans
      (sym (reopenExact receipt first))
      (trans
        (cong (reopen receipt commonClass) firstThirdEqual)
        (reopenExact receipt third)))
... | inj₂ (inj₂ secondThirdEqual) =
  pairwiseDistinct23
    (trans
      (sym (reopenExact receipt second))
      (trans
        (cong (reopen receipt commonClass) secondThirdEqual)
        (reopenExact receipt third)))

------------------------------------------------------------------------
-- Two bits suffice: 00, 01, 10 encode the three representatives.
------------------------------------------------------------------------

TwoBits : Set
TwoBits = Bool × Bool

twoBitResidual : Fine → TwoBits
twoBitResidual first = false , false
twoBitResidual second = false , true
twoBitResidual third = true , false

reopenTwoBits : Coarse → TwoBits → Fine
reopenTwoBits commonClass (false , false) = first
reopenTwoBits commonClass (false , true) = second
reopenTwoBits commonClass (true , false) = third
reopenTwoBits commonClass (true , true) = third

twoBitsReopenThreeStateFibreExactly :
  (state : Fine) → reopenTwoBits (coarsen state) (twoBitResidual state) ≡ state
twoBitsReopenThreeStateFibreExactly first = refl
twoBitsReopenThreeStateFibreExactly second = refl
twoBitsReopenThreeStateFibreExactly third = refl

------------------------------------------------------------------------
-- Hence this fibre realizes the exact fixed-length bound:
-- one bit is impossible and two bits suffice, i.e. ceil(log2 3) = 2.
------------------------------------------------------------------------
