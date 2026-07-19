module DASHI.Quantum.TSVFTests where

open import DASHI.Core.Prelude
open import DASHI.Foundations.TwoBoundarySystem
open import DASHI.Foundations.DiachronicFieldZeroToNine
open import DASHI.Foundations.DiachronicTwoBoundaryBridge
open import DASHI.Quantum.TSVF

------------------------------------------------------------------------
-- Tiny total witness for the abstract interfaces
--
-- This validates typing and laws only.  It is not a physical Hilbert model.
------------------------------------------------------------------------

toyQuantum : QuantumSurface
toyQuantum = record
  { Scalar = ⊤
  ; Weight = Bool
  ; Ket = ⊤
  ; Bra = ⊤
  ; Operator = ⊤
  ; Time = ⊤
  ; evolveKet = λ _ _ state → state
  ; evolveBra = λ _ _ state → state
  ; apply = λ _ state → state
  ; pair = λ _ _ → tt
  ; normSquared = λ _ → true
  ; divideWeight = λ _ _ → true
  ; Positive = λ weight → weight ≡ true
  }

toyEnsemble : TSVFEnsemble toyQuantum
toyEnsemble = prePostSelected tt tt tt tt tt

toyForwardState : forwardState toyEnsemble ≡ tt
toyForwardState = refl

toyBackwardState : backwardState toyEnsemble ≡ tt
toyBackwardState = refl

toyMeasurement : ProjectiveMeasurement toyQuantum
toyMeasurement = record
  { Outcome = ⊤
  ; projector = λ _ → tt
  ; totalPathWeight = λ _ → true
  }

toyABLContext : ABLContext toyQuantum toyMeasurement toyEnsemble
toyABLContext = ablContext refl

toyABLProbability :
  ablProbability toyABLContext tt ≡ true
toyABLProbability = refl

toyWeakSurface : WeakValueSurface toyQuantum
toyWeakSurface = record
  { divideScalar = λ _ _ → tt
  ; overlapAdmissible = λ _ → ⊤
  }

toyWeakContext :
  WeakValueContext toyQuantum toyWeakSurface toyEnsemble
toyWeakContext = weakContext tt

toyWeakValue :
  weakValue toyWeakSurface toyEnsemble toyWeakContext tt ≡ tt
toyWeakValue = refl

toyTimeReversal : TSVFTimeReversal toyQuantum
toyTimeReversal = record
  { reverseKet = λ state → state
  ; reverseBra = λ state → state
  ; reverseTime = λ time → time
  ; reverseKet-involutive = λ _ → refl
  ; reverseBra-involutive = λ _ → refl
  ; reverseTime-involutive = λ _ → refl
  ; ketEvolutionCovariant = λ _ _ _ → refl
  ; braEvolutionCovariant = λ _ _ _ → refl
  }

------------------------------------------------------------------------
-- Diachronic bridge witnesses
------------------------------------------------------------------------

exampleSixFoldRoundTrip :
  sixFold (sixFold exampleSixField) ≡ exampleSixField
exampleSixFoldRoundTrip = sixFold-involutive exampleSixField

exampleJunction : Junction diachronicSystem
exampleJunction =
  buildJunction
    diachronicPropagation
    rememberedUncertainty
    anticipatedAffirmation

exampleJunctionForwardClaim :
  PresentInterpretation.presentClaim
    (Junction.forwardLeg exampleJunction)
  ≡ indeterminate
exampleJunctionForwardClaim = refl

exampleJunctionBackwardClaim :
  PresentInterpretation.presentClaim
    (Junction.backwardLeg exampleJunction)
  ≡ transClaim
exampleJunctionBackwardClaim = refl
