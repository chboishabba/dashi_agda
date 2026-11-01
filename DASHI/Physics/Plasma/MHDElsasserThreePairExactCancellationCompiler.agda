module DASHI.Physics.Plasma.MHDElsasserThreePairExactCancellationCompiler where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Plasma.MHDFullTransferFromExchangeCompatiblePayloadExact as Pair

------------------------------------------------------------------------
-- THREE PAIRS -> ONE CYCLIC ELSASSER BALANCE
--
-- For one Elsasser species, a literal three-output triad can be partitioned
-- into the unordered exchange pairs {k,p}, {p,q}, {q,k}.  Each pair is closed
-- by the same exact exchange-compatible cancellation theorem.
------------------------------------------------------------------------

record ThreeExchangePairs {r : _} (F : C3.RealField r) : Set r where
  constructor three-exchange-pairs
  field
    kp pq qk : Pair.ExchangeCompatibleTransfer F
    sameLiteralTriadAcrossPairs : Set
    sameElsasserSpeciesAcrossPairs : Set
    pressureProjectionSameObjectReceipt : Set
    decompositionReference : String

open ThreeExchangePairs public

cyclicTransferSum :
  ∀ {r} {F : C3.RealField r} →
  ThreeExchangePairs F → C3.Carrier F
cyclicTransferSum {F = F} x =
  C3.add F
    (C3.add F
      (Pair.forwardTransfer (kp x))
      (Pair.reverseTransfer (kp x)))
    (C3.add F
      (C3.add F
        (Pair.forwardTransfer (pq x))
        (Pair.reverseTransfer (pq x)))
      (C3.add F
        (Pair.forwardTransfer (qk x))
        (Pair.reverseTransfer (qk x))))

threeExchangePairsCancelExactly :
  ∀ {r} {F : C3.RealField r}
    (x : ThreeExchangePairs F) →
  cyclicTransferSum x ≡ C3.zero F
threeExchangePairsCancelExactly {F = F} x
  rewrite Pair.pairTransferCancels (kp x)
        | Pair.pairTransferCancels (pq x)
        | Pair.pairTransferCancels (qk x) =
  R.solve 0
    ((R.Κ (C3.zero F) R.⊕
      (R.Κ (C3.zero F) R.⊕ R.Κ (C3.zero F)))
      R.⊜ R.Κ (C3.zero F))
    refl
  where module R = Field.Solver F

record ThreePairCompilerBoundary : Set where
  constructor three-pair-compiler-boundary
  field
    oneSkewPairClosesWholeTriad : Bool
    oneSkewPairClosesWholeTriadIsFalse :
      oneSkewPairClosesWholeTriad ≡ false

    allThreeExchangePairsCloseCyclicBalance : Bool
    allThreeExchangePairsCloseCyclicBalanceIsTrue :
      allThreeExchangePairsCloseCyclicBalance ≡ true

    plusSpeciesReceiptAutomaticallyClosesMinusSpecies : Bool
    plusSpeciesReceiptAutomaticallyClosesMinusSpeciesIsFalse :
      plusSpeciesReceiptAutomaticallyClosesMinusSpecies ≡ false

canonicalThreePairCompilerBoundary : ThreePairCompilerBoundary
canonicalThreePairCompilerBoundary =
  three-pair-compiler-boundary false refl true refl false refl
