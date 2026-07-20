module DASHI.Algebra.TriadicDepthTwoDFTGroupBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (neg; zer; pos; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicDepthTwoCyclotomicDFT as DFT9
import DASHI.Algebra.TriadicFiniteIrrep as Irrep

------------------------------------------------------------------------
-- Standard numeric labelling of Z/9Z by balanced-ternary residues.

indexToResidue : DFT9.Index9 → Q.Residue3Pow Q.two
indexToResidue DFT9.i0 = zer ∷ zer ∷ []
indexToResidue DFT9.i1 = pos ∷ zer ∷ []
indexToResidue DFT9.i2 = neg ∷ pos ∷ []
indexToResidue DFT9.i3 = zer ∷ pos ∷ []
indexToResidue DFT9.i4 = pos ∷ pos ∷ []
indexToResidue DFT9.i5 = neg ∷ neg ∷ []
indexToResidue DFT9.i6 = zer ∷ neg ∷ []
indexToResidue DFT9.i7 = pos ∷ neg ∷ []
indexToResidue DFT9.i8 = neg ∷ zer ∷ []

residueToIndex : Q.Residue3Pow Q.two → DFT9.Index9
residueToIndex (zer ∷ zer ∷ []) = DFT9.i0
residueToIndex (pos ∷ zer ∷ []) = DFT9.i1
residueToIndex (neg ∷ pos ∷ []) = DFT9.i2
residueToIndex (zer ∷ pos ∷ []) = DFT9.i3
residueToIndex (pos ∷ pos ∷ []) = DFT9.i4
residueToIndex (neg ∷ neg ∷ []) = DFT9.i5
residueToIndex (zer ∷ neg ∷ []) = DFT9.i6
residueToIndex (pos ∷ neg ∷ []) = DFT9.i7
residueToIndex (neg ∷ zer ∷ []) = DFT9.i8

indexRoundTrip :
  (i : DFT9.Index9) → residueToIndex (indexToResidue i) ≡ i
indexRoundTrip DFT9.i0 = refl
indexRoundTrip DFT9.i1 = refl
indexRoundTrip DFT9.i2 = refl
indexRoundTrip DFT9.i3 = refl
indexRoundTrip DFT9.i4 = refl
indexRoundTrip DFT9.i5 = refl
indexRoundTrip DFT9.i6 = refl
indexRoundTrip DFT9.i7 = refl
indexRoundTrip DFT9.i8 = refl

residueRoundTrip :
  (r : Q.Residue3Pow Q.two) → indexToResidue (residueToIndex r) ≡ r
residueRoundTrip (zer ∷ zer ∷ []) = refl
residueRoundTrip (pos ∷ zer ∷ []) = refl
residueRoundTrip (neg ∷ pos ∷ []) = refl
residueRoundTrip (zer ∷ pos ∷ []) = refl
residueRoundTrip (pos ∷ pos ∷ []) = refl
residueRoundTrip (neg ∷ neg ∷ []) = refl
residueRoundTrip (zer ∷ neg ∷ []) = refl
residueRoundTrip (pos ∷ neg ∷ []) = refl
residueRoundTrip (neg ∷ zer ∷ []) = refl

------------------------------------------------------------------------
-- The labelling is an additive-group isomorphism, not merely an enumeration.

indexAdditionMatchesResidue :
  (x y : DFT9.Index9) →
  Arithmetic.addResidue (indexToResidue x) (indexToResidue y)
  ≡ indexToResidue (DFT9.addIndex x y)
indexAdditionMatchesResidue DFT9.i0 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i0 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i1 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i2 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i3 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i4 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i5 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i6 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i7 DFT9.i8 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i0 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i1 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i2 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i3 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i4 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i5 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i6 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i7 = refl
indexAdditionMatchesResidue DFT9.i8 DFT9.i8 = refl

------------------------------------------------------------------------
-- Group-aligned signal packing and exact codec.

packGroupSignal : Irrep.Signal Q.two DFT9.C9 → DFT9.Signal9
packGroupSignal f = DFT9.signal9
    (f (indexToResidue DFT9.i0))
    (f (indexToResidue DFT9.i1))
    (f (indexToResidue DFT9.i2))
    (f (indexToResidue DFT9.i3))
    (f (indexToResidue DFT9.i4))
    (f (indexToResidue DFT9.i5))
    (f (indexToResidue DFT9.i6))
    (f (indexToResidue DFT9.i7))
    (f (indexToResidue DFT9.i8))

unpackGroupSignal : DFT9.Signal9 → Irrep.Signal Q.two DFT9.C9
unpackGroupSignal spectrum residue =
  DFT9.atSignal spectrum (residueToIndex residue)

groupAlignedDepthTwoCodec : Irrep.ExactSpectralCodec Q.two
groupAlignedDepthTwoCodec =
  record
    { Coeff = DFT9.C9
    ; Spectrum = DFT9.Signal9
    ; analyze = λ f → DFT9.analyze9 (packGroupSignal f)
    ; synthesize = λ spectrum →
        unpackGroupSignal (DFT9.synthesize9 spectrum)
    ; reconstructAnalyze = reconstruct
    ; spectralWidth = Q.pow3 Q.two
    ; spectralWidthMatchesQuotient = refl
    }
  where
  reconstruct :
    (f : Irrep.Signal Q.two DFT9.C9) →
    (r : Q.Residue3Pow Q.two) →
    unpackGroupSignal
      (DFT9.synthesize9 (DFT9.analyze9 (packGroupSignal f))) r
    ≡ f r
  reconstruct f (zer ∷ zer ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i0
  reconstruct f (pos ∷ zer ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i1
  reconstruct f (neg ∷ pos ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i2
  reconstruct f (zer ∷ pos ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i3
  reconstruct f (pos ∷ pos ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i4
  reconstruct f (neg ∷ neg ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i5
  reconstruct f (zer ∷ neg ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i6
  reconstruct f (pos ∷ neg ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i7
  reconstruct f (neg ∷ zer ∷ []) =
    DFT9.reconstructAnalyze9 (packGroupSignal f) DFT9.i8

groupBridgeStatement : String
groupBridgeStatement =
  "The numeric Index9 carrier is proved additively isomorphic to the balanced-ternary quotient Z/9Z; the exact cyclotomic DFT is therefore applied using genuine group labels rather than an arbitrary coordinate permutation."
