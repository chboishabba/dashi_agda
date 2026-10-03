module DASHI.Core.IndexedRelationalPadicWaveContinuousAdaptersExact where

------------------------------------------------------------------------
-- EXISTING OWNER WELD, not a new 369/p-adic/wave ontology.
--
-- Finite-prefix p-adic addresses: SSP369Ultrametric and
-- PadicCylinderLODReasoningField.
-- Continuous-indexed symbolic streams: BalancedTernaryContinuousEnvelope.
-- Wave / exact symbolic coefficient carriers:
-- Base369WaveContinuousSymbolicCodingExact and ShiftWaveRefinementSeam.
-- Generic factorisation: IndexedRelationalHyperfabricSpineExact.
--
-- Analytic boundary: BalancedTernaryContinuousEnvelope's Stream is
-- Nat -> Trit, NOT an assertion that an analytic continuous Euclidean
-- completion or physical wave solution has been constructed.
-- Wave coarse/fine seam itself explicitly does NOT assert a collision.
-- The p-adic and stream examples here are exact *finite-depth* collisions;
-- none confers legal/cultural authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Geometry.SSP369Ultrametric as U
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Stream
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Symbolic
import DASHI.Physics.ShiftWaveRefinementSeam as Wave
import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as WaveState

------------------------------------------------------------------------
-- Exact p-adic prefix / general B^k address identity.
------------------------------------------------------------------------

padicAddressIsGeneric :
  (k : Nat) → U.Address k → Core.Address U.Digit369 k
padicAddressIsGeneric k address = address

prefixOne : U.Address 2 → U.Address 1
prefixOne = LOD.prefixTwoToOne

secondDigit : U.Address 2 → U.Digit369
secondDigit (a ∷ b ∷ []) = b

pair3 : U.Address 2
pair3 = U.digit3 ∷ U.digit3 ∷ []

pair6 : U.Address 2
pair6 = U.digit3 ∷ U.digit6 ∷ []

secondDigitDifferent :
  secondDigit pair3 ≡ secondDigit pair6 → ⊥
secondDigitDifferent ()

prefixHasExactCollision :
  Core.ConsumerCollision prefixOne secondDigit
prefixHasExactCollision =
  NF.nonFactorabilityWitness pair3 pair6 refl secondDigitDifferent

padicPrefixCannotDetermineDiscardedDigit :
  Core.ConsumerSufficient prefixOne secondDigit → ⊥
padicPrefixCannotDetermineDiscardedDigit =
  Core.collisionRefutesSufficiency prefixHasExactCollision

------------------------------------------------------------------------
-- Arbitrary wave/continuous carrier preserves its exact state *when*
-- the symbolic address is a component of an evidence-bearing full state.
-- Do not assert that the quantized trit alone can recover amplitudes!
------------------------------------------------------------------------

symbolicEncodedStateIsSufficient :
  ∀ {Carrier : Set}
  (coding : Symbolic.SymbolicCoding Carrier) →
  Core.ConsumerSufficient
    (Symbolic.encode coding)
    (λ (x : Carrier) → x)
symbolicEncodedStateIsSufficient coding =
  NF.factorsThrough
    Symbolic.decode
    (Symbolic.decodeAfterEncode coding)

------------------------------------------------------------------------
-- Existing wave seam: ONLY the checked project/fine agreement transported.
-- The source module does not supply a static collision witness, so this
-- adapter does not promote a wave nonfactorability theorem.
------------------------------------------------------------------------

waveFineRecoversCoarse :
  Core.ConsumerSufficient Wave.fineObserve Wave.coarseObserve
waveFineRecoversCoarse =
  NF.factorsThrough
    Wave.projectFine
    Wave.projectFineAgreement-witness

------------------------------------------------------------------------
-- Infinite symbolic streams (a genuine Nat-indexed domain), evaluated at
-- finite precision. Agreement at depth 2 does not reconstruct digit 3.
-- This is combinatorial, NOT a real/analytic completion theorem.
------------------------------------------------------------------------

sameEverywhere : Stream.Stream
sameEverywhere n = Stream.neg

changedThird : Stream.Stream
changedThird zero = Stream.neg
changedThird (suc zero) = Stream.neg
changedThird (suc (suc zero)) = Stream.pos
changedThird (suc (suc (suc n))) = Stream.neg

thirdPrefixDifferent :
  Stream.take 3 sameEverywhere ≡
  Stream.take 3 changedThird → ⊥
thirdPrefixDifferent ()

twoPrefixCollision :
  Core.ConsumerCollision
    (Stream.take 2) (Stream.take 3)
twoPrefixCollision =
  NF.nonFactorabilityWitness
    sameEverywhere changedThird refl thirdPrefixDifferent

twoDigitViewCannotAnswerThirdDigit :
  Core.ConsumerSufficient
    (Stream.take 2) (Stream.take 3) → ⊥
twoDigitViewCannotAnswerThirdDigit =
  Core.collisionRefutesSufficiency twoPrefixCollision

-- Same obstruction survives any chart / re-encoding of the two-trit
-- prefix. This is precisely the existing query-sensitive fibre theorem.
twoDigitRechartCannotRecoverThird :
  ∀ {Chart : Set} (chart : Stream.TritPrefix 2 → Chart) →
  Core.ConsumerSufficient
    (λ s → chart (Stream.take 2 s))
    (Stream.take 3) → ⊥
twoDigitRechartCannotRecoverThird chart =
  Core.collisionSurvivesRechart chart twoPrefixCollision
