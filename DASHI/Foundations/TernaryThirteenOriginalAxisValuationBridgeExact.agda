module DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact where

------------------------------------------------------------------------
-- H1.01, source-carrier stage: original 12 StageAtlas addresses,
-- original Base369.TriTruth values, and one chosen central TriTruth.
-- This is the newly CONSTRUCTED source valuation model, not an
-- identification with Monster 3^(1+12) or the 144-edge relation field.
-- No functional extensionality: prove the correct *pointwise* inverse.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.TernaryThirteenFibreSplitExact as F
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as P
import Base369 as Base

toSource : F.Trit → Base.TriTruth
toSource F.negative = Base.tri-low
toSource F.neutral = Base.tri-mid
toSource F.positive = Base.tri-high

fromSource : Base.TriTruth → F.Trit
fromSource Base.tri-low = F.negative
fromSource Base.tri-mid = F.neutral
fromSource Base.tri-high = F.positive

toFromSource :
  (value : Base.TriTruth) → toSource (fromSource value) ≡ value
toFromSource Base.tri-low = refl
toFromSource Base.tri-mid = refl
toFromSource Base.tri-high = refl

fromToSource :
  (value : F.Trit) → fromSource (toSource value) ≡ value
fromToSource F.negative = refl
fromToSource F.neutral = refl
fromToSource F.positive = refl

wordToValuation : F.TritWord 12 → Rel.SourceTwelveAxisValuation
wordToValuation word Atlas.atlas-0 = toSource (proj₁ (word))
wordToValuation word Atlas.atlas-1 = toSource (proj₁ (proj₂ (word)))
wordToValuation word Atlas.atlas-2 = toSource (proj₁ (proj₂ (proj₂ (word))))
wordToValuation word Atlas.atlas-3 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (word)))))
wordToValuation word Atlas.atlas-4 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (word))))))
wordToValuation word Atlas.atlas-5 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word)))))))
wordToValuation word Atlas.atlas-6 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word))))))))
wordToValuation word Atlas.atlas-7 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word)))))))))
wordToValuation word Atlas.atlas-8 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word))))))))))
wordToValuation word Atlas.atlas-9 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word)))))))))))
wordToValuation word Atlas.atlas-10 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word))))))))))))
wordToValuation word Atlas.atlas-11 = toSource (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (word)))))))))))))

valuationToWord : Rel.SourceTwelveAxisValuation → F.TritWord 12
valuationToWord valuation = (fromSource (valuation Atlas.atlas-0) , (fromSource (valuation Atlas.atlas-1) , (fromSource (valuation Atlas.atlas-2) , (fromSource (valuation Atlas.atlas-3) , (fromSource (valuation Atlas.atlas-4) , (fromSource (valuation Atlas.atlas-5) , (fromSource (valuation Atlas.atlas-6) , (fromSource (valuation Atlas.atlas-7) , (fromSource (valuation Atlas.atlas-8) , (fromSource (valuation Atlas.atlas-9) , (fromSource (valuation Atlas.atlas-10) , (fromSource (valuation Atlas.atlas-11) , tt))))))))))))

mapTritWord :
  (n : Nat) → (F.Trit → F.Trit) →
  F.TritWord n → F.TritWord n
mapTritWord zero map tt = tt
mapTritWord (suc n) map (x , xs) =
  map x , mapTritWord n map xs

mapFromToRoundTrip :
  (n : Nat) (word : F.TritWord n) →
  mapTritWord n (λ x → fromSource (toSource x)) word ≡ word
mapFromToRoundTrip zero tt = refl
mapFromToRoundTrip (suc n) (x , xs) =
  cong₂ _,_ (fromToSource x) (mapFromToRoundTrip n xs)

valuationWordRoundTrip :
  (word : F.TritWord 12) →
  valuationToWord (wordToValuation word) ≡ word
-- Explicitly eliminate the 12 nested pairs. The projection-based
-- valuationToWord is NOT definitionally equal to the recursive
-- mapTritWord on an *unsplit* variable word.
valuationWordRoundTrip (x0 , (x1 , (x2 , (x3 , (x4 , (x5 , (x6 , (x7 , (x8 , (x9 , (x10 , (x11 , tt)))))))))))) =
  cong₂ _,_ (fromToSource x0)
    (cong₂ _,_ (fromToSource x1)
    (cong₂ _,_ (fromToSource x2)
    (cong₂ _,_ (fromToSource x3)
    (cong₂ _,_ (fromToSource x4)
    (cong₂ _,_ (fromToSource x5)
    (cong₂ _,_ (fromToSource x6)
    (cong₂ _,_ (fromToSource x7)
    (cong₂ _,_ (fromToSource x8)
    (cong₂ _,_ (fromToSource x9)
    (cong₂ _,_ (fromToSource x10)
    (cong₂ _,_ (fromToSource x11)
    (refl))))))))))))

valuationPointwiseRoundTrip :
  (valuation : Rel.SourceTwelveAxisValuation)
  (axis : Atlas.StageAtlasZeroToEleven) →
  wordToValuation (valuationToWord valuation) axis ≡ valuation axis
valuationPointwiseRoundTrip valuation Atlas.atlas-0 =
  toFromSource (valuation Atlas.atlas-0)
valuationPointwiseRoundTrip valuation Atlas.atlas-1 =
  toFromSource (valuation Atlas.atlas-1)
valuationPointwiseRoundTrip valuation Atlas.atlas-2 =
  toFromSource (valuation Atlas.atlas-2)
valuationPointwiseRoundTrip valuation Atlas.atlas-3 =
  toFromSource (valuation Atlas.atlas-3)
valuationPointwiseRoundTrip valuation Atlas.atlas-4 =
  toFromSource (valuation Atlas.atlas-4)
valuationPointwiseRoundTrip valuation Atlas.atlas-5 =
  toFromSource (valuation Atlas.atlas-5)
valuationPointwiseRoundTrip valuation Atlas.atlas-6 =
  toFromSource (valuation Atlas.atlas-6)
valuationPointwiseRoundTrip valuation Atlas.atlas-7 =
  toFromSource (valuation Atlas.atlas-7)
valuationPointwiseRoundTrip valuation Atlas.atlas-8 =
  toFromSource (valuation Atlas.atlas-8)
valuationPointwiseRoundTrip valuation Atlas.atlas-9 =
  toFromSource (valuation Atlas.atlas-9)
valuationPointwiseRoundTrip valuation Atlas.atlas-10 =
  toFromSource (valuation Atlas.atlas-10)
valuationPointwiseRoundTrip valuation Atlas.atlas-11 =
  toFromSource (valuation Atlas.atlas-11)

-- Encode the SOURCE original-axis valuation model as one 13-word.
sourceCentralToThirteen :
  Rel.SourceCentralCompletionCarrier → F.TritWord 13
sourceCentralToThirteen (valuation , center) =
  F.ternaryThirteenJoinTwelvePlusOne
    (valuationToWord valuation , P.singleTrit (fromSource center))

thirteenToSourceCentral :
  F.TritWord 13 → Rel.SourceCentralCompletionCarrier
thirteenToSourceCentral word =
  wordToValuation
    (proj₁ (F.ternaryThirteenSplitTwelvePlusOne word)) ,
  toSource (P.lastTrit word)

sourceCentralRoundTripOnAxis :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (thirteenToSourceCentral (sourceCentralToThirteen state)) axis
  ≡ proj₁ state axis
sourceCentralRoundTripOnAxis (valuation , center) axis
  rewrite F.ternaryThirteenSplitRoundTrip
    (valuationToWord valuation , P.singleTrit (fromSource center)) =
  valuationPointwiseRoundTrip valuation axis

sourceCentralRoundTripOnCentre :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (thirteenToSourceCentral (sourceCentralToThirteen state))
  ≡ proj₂ state
sourceCentralRoundTripOnCentre (valuation , center)
  rewrite F.ternaryThirteenSplitRoundTrip
    (valuationToWord valuation , P.singleTrit (fromSource center)) =
  toFromSource center

-- The 13-word inverse is a full propositional equality, not just
-- pointwise: the finite word carrier has ordinary inductive equality.
thirteenSourceRoundTrip :
  (word : F.TritWord 13) →
  sourceCentralToThirteen (thirteenToSourceCentral word) ≡ word
thirteenSourceRoundTrip word
  with F.ternaryThirteenSplitTwelvePlusOne word
... | prefix , (center , tt) =
  trans
    (cong (λ q → F.ternaryThirteenJoinTwelvePlusOne
            (q , P.singleTrit (fromSource (toSource center))))
      (valuationWordRoundTrip prefix))
    (trans
      (cong (λ q → F.ternaryThirteenJoinTwelvePlusOne
          (prefix , P.singleTrit q)) (fromToSource center))
      (F.ternaryThirteenJoinRoundTrip word))

-- The semantic source-neutral section is represented exactly by
-- the previously constructed final-neutral word section.
sourceNeutralSectionCommutes :
  (valuation : Rel.SourceTwelveAxisValuation) →
  sourceCentralToThirteen (Rel.sourceNeutralSection valuation)
  ≡ P.centralCoordinateZeroSection (valuationToWord valuation)
sourceNeutralSectionCommutes valuation = refl
