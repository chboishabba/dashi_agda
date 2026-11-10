module DASHI.Physics.Motors.FilsingerMeterSignNonidentifiabilityExact where

-- Finite proof: a negative meter SIGN alone cannot identify the
-- capacitor's terminal-to-terminal polarity, let alone Earth energy.
-- Not a voltage calculation, wiring claim or empirical test.
-- Source: user-supplied Filsinger recording; narrator's reported meter flip.
-- Mathematical counterworlds authored by DASHI, not attributed to Filsinger.

open import Agda.Builtin.Equality using (_≡_; refl)

data Contradiction : Set where

data Sign : Set where
  positive negative : Sign

-- Counterworlds have the same meter sign but different hidden
-- physical capacitor sign. Other physical states are left unmodelled.
data CandidateWorld : Set where
  floatingReference : CandidateWorld
  actualCapacitorReversal : CandidateWorld

meterSign : CandidateWorld → Sign
meterSign floatingReference = negative
meterSign actualCapacitorReversal = negative

capacitorSign : CandidateWorld → Sign
capacitorSign floatingReference = positive
capacitorSign actualCapacitorReversal = negative

sameNegativeMeter :
  meterSign floatingReference ≡ meterSign actualCapacitorReversal
sameNegativeMeter = refl

capacitorSignsDistinct : positive ≡ negative → Contradiction
capacitorSignsDistinct ()

MeterSignDeterminesCapacitorSign : Set
MeterSignDeterminesCapacitorSign =
  (x y : CandidateWorld) →
  meterSign x ≡ meterSign y →
  capacitorSign x ≡ capacitorSign y

meterSignDoesNotIdentifyCapacitorPolarity :
  MeterSignDeterminesCapacitorSign → Contradiction
meterSignDoesNotIdentifyCapacitorPolarity determines =
  capacitorSignsDistinct
    (determines floatingReference actualCapacitorReversal sameNegativeMeter)

-- Physical realization remains conditional: the distinct worlds
-- are finite structural witnesses, not verified apparatus conditions.
