module DASHI.Mathematics.Topology.AlexanderHornedFiveOrbitNamedWordWaveTransportExact where

------------------------------------------------------------------------
-- Actual finite observation-domain transport (NOT a physical weld):
-- SOURCE five-orbit operator fields on native n=2 end addresses
--  -> named 3-label words modulo global value S3.
--
-- Reuses original #1244 five-orbit, wave-operator and canonical
-- anchored S3/C2 word-sign transport owner. Does NOT import unmerged
-- #1275; its five RGS equality-pattern classes have the SAME sourced
-- three-label action and table, but independent mathematical ownership.
--
-- Source-written, kernel-pending; no actual acoustic/NS/RH/Monster/
-- native wild-horn physical wave or signal-equivalence claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedS3WordSignOrbitTransportExact as Word
import DASHI.Mathematics.Topology.AlexanderHornedDepthTwoFiveOrbitFibreExact as Five
import DASHI.Mathematics.Topology.AlexanderHornedFiveOrbitWaveOperatorExact as Operator

NamedThreeWord : Set
NamedThreeWord = Word.AnchoredWord 2

twoDigitOrbit : End.BalancedLevel 2 → Five.FiveOrbit
twoDigitOrbit (sector , (a ∷ b ∷ [])) = Five.orbit a b

wordOrbit : NamedThreeWord → Five.FiveOrbit
wordOrbit w with Word.signedRelative w
... | (a ∷ b ∷ []) = Five.orbit a b

-- Global named-value translation loses its 3-fold label anchor.
wordOrbitTranslationInvariant : (shift : C3.C3)
  (w : NamedThreeWord) →
  wordOrbit (Word.translateWord shift w) ≡ wordOrbit w
wordOrbitTranslationInvariant shift w =
  cong orbitFromSigned (Word.signedRelativeTranslationInvariant shift w)
  where
    orbitFromSigned : ∀ {n} → End.BalancedLevel 2 → Five.FiveOrbit
    orbitFromSigned (sector , (a ∷ b ∷ [])) = Five.orbit a b

-- This is a genuine C2 residual reflection relation, not a new S3.
orbitReflectTwo : (xs : End.BalancedLevel 2) →
  twoDigitOrbit (End.reflectBalancedLevel 2 xs) ≡ twoDigitOrbit xs
orbitReflectTwo (sector , (a ∷ b ∷ [])) = Five.orbitReflect a b

-- Named representatives of the ORIGINAL five equality patterns.
aaa : NamedThreeWord
aaa = C3.c0 , (C3.c0 ∷ C3.c0 ∷ [])
aab : NamedThreeWord
aab = C3.c0 , (C3.c0 ∷ C3.c1 ∷ [])
aba : NamedThreeWord
aba = C3.c0 , (C3.c1 ∷ C3.c0 ∷ [])
abb : NamedThreeWord
abb = C3.c0 , (C3.c1 ∷ C3.c1 ∷ [])
abc : NamedThreeWord
abc = C3.c0 , (C3.c1 ∷ C3.c2 ∷ [])

aaaOrbit : wordOrbit aaa ≡ Five.origin
aaaOrbit = refl
aabOrbit : wordOrbit aab ≡ Five.axisSecond
aabOrbit = refl
abaOrbit : wordOrbit aba ≡ Five.axisFirst
abaOrbit = refl
abbOrbit : wordOrbit abb ≡ Five.diagonal
abbOrbit = refl
abcOrbit : wordOrbit abc ≡ Five.antiDiagonal
abcOrbit = refl

namedWaveField : Operator.FiveWaveField → NamedThreeWord →
  Wave.DiscreteWave
namedWaveField f w = f (wordOrbit w)

namedWaveOperator : Operator.FiveOperatorField →
  NamedThreeWord → Operator.WaveOperator
namedWaveOperator op w = op (wordOrbit w)

namedEvolution : Operator.FiveOperatorField → Operator.FiveWaveField →
  NamedThreeWord → Wave.DiscreteWave
namedEvolution op f w = namedWaveOperator op w (namedWaveField f w)

namedEvolutionFactor : ∀ op f w →
  namedEvolution op f w ≡ Operator.evolveFive op f (wordOrbit w)
namedEvolutionFactor op f w = refl

namedWaveTranslationInvariant : ∀ f shift w →
  namedWaveField f (Word.translateWord shift w) ≡ namedWaveField f w
namedWaveTranslationInvariant f shift w =
  cong f (wordOrbitTranslationInvariant shift w)

-- Other S3 value permutations require the residual sign proof from
-- Word.signedRelativeReflection and Five.orbitReflect. The true wave
-- actor remains Operator.FiveWaveField on #1244's H orbit quotient.
