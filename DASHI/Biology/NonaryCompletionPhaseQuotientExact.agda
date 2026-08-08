module DASHI.Biology.NonaryCompletionPhaseQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves",
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Replace the numerical slogan 10 / 2 = 5 by an explicit quotient carrier.
-- The ten states are the nine ordinary balanced-pair channels together with
-- the distinguished completion channel j.  Complement pairs them as
--
--   {0,j}, {1,8}, {2,7}, {3,6}, {4,5}.
--
-- Encoding a state records its complement mode and its binary phase.  Decoding
-- is a two-sided inverse, and complement preserves the mode while flipping the
-- phase.  The ten-state carrier is also proved isomorphic to the repository's
-- existing T^2 disjoint-union {j} coarse carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic

------------------------------------------------------------------------
-- Ten-state completed nonary carrier.
------------------------------------------------------------------------

data DecimalCompletionState : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 j9 : DecimalCompletionState

data ComplementMode5 : Set where
  mode09 mode18 mode27 mode36 mode45 : ComplementMode5

data BinaryPhase : Set where
  directPhase counterPhase : BinaryPhase

flipBinaryPhase : BinaryPhase → BinaryPhase
flipBinaryPhase directPhase = counterPhase
flipBinaryPhase counterPhase = directPhase

flipBinaryPhaseInvolutive :
  (phase : BinaryPhase) →
  flipBinaryPhase (flipBinaryPhase phase) ≡ phase
flipBinaryPhaseInvolutive directPhase = refl
flipBinaryPhaseInvolutive counterPhase = refl

complementState : DecimalCompletionState → DecimalCompletionState
complementState d0 = j9
complementState d1 = d8
complementState d2 = d7
complementState d3 = d6
complementState d4 = d5
complementState d5 = d4
complementState d6 = d3
complementState d7 = d2
complementState d8 = d1
complementState j9 = d0

complementStateInvolutive :
  (state : DecimalCompletionState) →
  complementState (complementState state) ≡ state
complementStateInvolutive d0 = refl
complementStateInvolutive d1 = refl
complementStateInvolutive d2 = refl
complementStateInvolutive d3 = refl
complementStateInvolutive d4 = refl
complementStateInvolutive d5 = refl
complementStateInvolutive d6 = refl
complementStateInvolutive d7 = refl
complementStateInvolutive d8 = refl
complementStateInvolutive j9 = refl

encodeModePhase : DecimalCompletionState → ComplementMode5 × BinaryPhase
encodeModePhase d0 = mode09 , directPhase
encodeModePhase d1 = mode18 , directPhase
encodeModePhase d2 = mode27 , directPhase
encodeModePhase d3 = mode36 , directPhase
encodeModePhase d4 = mode45 , directPhase
encodeModePhase d5 = mode45 , counterPhase
encodeModePhase d6 = mode36 , counterPhase
encodeModePhase d7 = mode27 , counterPhase
encodeModePhase d8 = mode18 , counterPhase
encodeModePhase j9 = mode09 , counterPhase

decodeModePhase : ComplementMode5 × BinaryPhase → DecimalCompletionState
decodeModePhase (mode09 , directPhase) = d0
decodeModePhase (mode09 , counterPhase) = j9
decodeModePhase (mode18 , directPhase) = d1
decodeModePhase (mode18 , counterPhase) = d8
decodeModePhase (mode27 , directPhase) = d2
decodeModePhase (mode27 , counterPhase) = d7
decodeModePhase (mode36 , directPhase) = d3
decodeModePhase (mode36 , counterPhase) = d6
decodeModePhase (mode45 , directPhase) = d4
decodeModePhase (mode45 , counterPhase) = d5

decodeAfterEncode :
  (state : DecimalCompletionState) →
  decodeModePhase (encodeModePhase state) ≡ state
decodeAfterEncode d0 = refl
decodeAfterEncode d1 = refl
decodeAfterEncode d2 = refl
decodeAfterEncode d3 = refl
decodeAfterEncode d4 = refl
decodeAfterEncode d5 = refl
decodeAfterEncode d6 = refl
decodeAfterEncode d7 = refl
decodeAfterEncode d8 = refl
decodeAfterEncode j9 = refl

encodeAfterDecode :
  (modePhase : ComplementMode5 × BinaryPhase) →
  encodeModePhase (decodeModePhase modePhase) ≡ modePhase
encodeAfterDecode (mode09 , directPhase) = refl
encodeAfterDecode (mode09 , counterPhase) = refl
encodeAfterDecode (mode18 , directPhase) = refl
encodeAfterDecode (mode18 , counterPhase) = refl
encodeAfterDecode (mode27 , directPhase) = refl
encodeAfterDecode (mode27 , counterPhase) = refl
encodeAfterDecode (mode36 , directPhase) = refl
encodeAfterDecode (mode36 , counterPhase) = refl
encodeAfterDecode (mode45 , directPhase) = refl
encodeAfterDecode (mode45 , counterPhase) = refl

complementMode : DecimalCompletionState → ComplementMode5
complementMode state = Data.Product.proj₁ (encodeModePhase state)

binaryPhase : DecimalCompletionState → BinaryPhase
binaryPhase state = Data.Product.proj₂ (encodeModePhase state)

complementPreservesMode :
  (state : DecimalCompletionState) →
  complementMode (complementState state) ≡ complementMode state
complementPreservesMode d0 = refl
complementPreservesMode d1 = refl
complementPreservesMode d2 = refl
complementPreservesMode d3 = refl
complementPreservesMode d4 = refl
complementPreservesMode d5 = refl
complementPreservesMode d6 = refl
complementPreservesMode d7 = refl
complementPreservesMode d8 = refl
complementPreservesMode j9 = refl

complementFlipsBinaryPhase :
  (state : DecimalCompletionState) →
  binaryPhase (complementState state)
  ≡ flipBinaryPhase (binaryPhase state)
complementFlipsBinaryPhase d0 = refl
complementFlipsBinaryPhase d1 = refl
complementFlipsBinaryPhase d2 = refl
complementFlipsBinaryPhase d3 = refl
complementFlipsBinaryPhase d4 = refl
complementFlipsBinaryPhase d5 = refl
complementFlipsBinaryPhase d6 = refl
complementFlipsBinaryPhase d7 = refl
complementFlipsBinaryPhase d8 = refl
complementFlipsBinaryPhase j9 = refl

------------------------------------------------------------------------
-- Exact reuse of T^2 disjoint-union {j}.
------------------------------------------------------------------------

toCoarseChannel : DecimalCompletionState → Harmonic.CoarseChannel
toCoarseChannel d0 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)
toCoarseChannel d1 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)
toCoarseChannel d2 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)
toCoarseChannel d3 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)
toCoarseChannel d4 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)
toCoarseChannel d5 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)
toCoarseChannel d6 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)
toCoarseChannel d7 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)
toCoarseChannel d8 =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)
toCoarseChannel j9 = Harmonic.completionJ

fromCoarseChannel : Harmonic.CoarseChannel → DecimalCompletionState
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = d0
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = d1
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = d2
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = d3
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = d4
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = d5
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = d6
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = d7
fromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = d8
fromCoarseChannel Harmonic.completionJ = j9

fromAfterToCoarseChannel :
  (state : DecimalCompletionState) →
  fromCoarseChannel (toCoarseChannel state) ≡ state
fromAfterToCoarseChannel d0 = refl
fromAfterToCoarseChannel d1 = refl
fromAfterToCoarseChannel d2 = refl
fromAfterToCoarseChannel d3 = refl
fromAfterToCoarseChannel d4 = refl
fromAfterToCoarseChannel d5 = refl
fromAfterToCoarseChannel d6 = refl
fromAfterToCoarseChannel d7 = refl
fromAfterToCoarseChannel d8 = refl
fromAfterToCoarseChannel j9 = refl

toAfterFromCoarseChannel :
  (channel : Harmonic.CoarseChannel) →
  toCoarseChannel (fromCoarseChannel channel) ≡ channel
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = refl
toAfterFromCoarseChannel
  (Harmonic.ordinaryChannel
    (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = refl
toAfterFromCoarseChannel Harmonic.completionJ = refl

------------------------------------------------------------------------
-- Finite cardinality certificates.
------------------------------------------------------------------------

canonicalDecimalCompletionStates : List DecimalCompletionState
canonicalDecimalCompletionStates =
  d0 ∷ d1 ∷ d2 ∷ d3 ∷ d4 ∷ d5 ∷ d6 ∷ d7 ∷ d8 ∷ j9 ∷ []

canonicalComplementModes : List ComplementMode5
canonicalComplementModes = mode09 ∷ mode18 ∷ mode27 ∷ mode36 ∷ mode45 ∷ []

canonicalBinaryPhases : List BinaryPhase
canonicalBinaryPhases = directPhase ∷ counterPhase ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

decimalCompletionStateCountIsTen :
  listCount canonicalDecimalCompletionStates ≡ 10
decimalCompletionStateCountIsTen = refl

complementModeCountIsFive : listCount canonicalComplementModes ≡ 5
complementModeCountIsFive = refl

binaryPhaseCountIsTwo : listCount canonicalBinaryPhases ≡ 2
binaryPhaseCountIsTwo = refl

tenIsFiveTimesTwo : 10 ≡ 5 * 2
tenIsFiveTimesTwo = refl

record NonaryCompletionQuotientBoundary : Set where
  constructor nonary-completion-quotient-boundary
  field
    tenStateQuotientConstructed : Bool
    tenStateQuotientConstructedIsTrue : tenStateQuotientConstructed ≡ true
    completionJIdentifiedWithOrdinaryTorusResidue : Bool
    completionJIdentifiedWithOrdinaryTorusResidueIsFalse :
      completionJIdentifiedWithOrdinaryTorusResidue ≡ false
    quotientModeSemanticsProveD4IrrepSemantics : Bool
    quotientModeSemanticsProveD4IrrepSemanticsIsFalse :
      quotientModeSemanticsProveD4IrrepSemantics ≡ false

canonicalNonaryCompletionQuotientBoundary : NonaryCompletionQuotientBoundary
canonicalNonaryCompletionQuotientBoundary =
  nonary-completion-quotient-boundary true refl false refl false refl
