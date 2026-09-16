module DASHI.Law.SensibLawWoogarooScenicPeninsulaVisualLandscapeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCENIC / PENINSULA VISUAL LANDSCAPE SNOWBALL
--
-- Source role: Saunders Havill Group 2020 proponent-side ecological material
-- prepared for Springfield City Group.  These are technical/proponent claims
-- and rendered-map observations, not Commonwealth adjudicated findings.
------------------------------------------------------------------------

data Project : Set where
  peninsula20208629 : Project
  scenic20208651 : Project

record VisualLandscapeReceipt : Set where
  constructor visual-landscape-receipt
  field
    project : Project
    carrier : String
    pageOrPlan : String
    observation : String
    attribution : String
    consumer : String
    residual : String

open VisualLandscapeReceipt public

peninsulaCriticalKoala : VisualLandscapeReceipt
peninsulaCriticalKoala = visual-landscape-receipt
  peninsula20208629
  "2020-8629 7399_EPBC_REFERRAL_PENINSULA_PRECINCT_opt_2.pdf"
  "rendered PDF page 27 / Plan 4"
  "Plan maps potential critical Koala habitat across most of the referral area and labels 17.08 ha habitat to remove."
  "Saunders Havill Group, 2 March 2020"
  "EPBC significant-impact / cumulative-fragmentation / offset consumer"
  "Proponent technical map; later Preliminary Documentation or Commonwealth decision may refine the assessment."

peninsulaContiguous675 : VisualLandscapeReceipt
peninsulaContiguous675 = visual-landscape-receipt
  peninsula20208629
  "2020-8629 7399_EPBC_REFERRAL_PENINSULA_PRECINCT_opt_2.pdf"
  "rendered PDF page 28 / Plan 5"
  "Plan depicts Peninsula at the southern end of a mapped 675 ha contiguous landscape."
  "Saunders Havill Group, 2 March 2020"
  "EPBC connectivity / cumulative fragmentation / Queensland habitat-function acquisition"
  "Desktop landscape model; does not by itself prove statutory critical habitat or exact current corridor geometry."

scenicCriticalKoala : VisualLandscapeReceipt
scenicCriticalKoala = visual-landscape-receipt
  scenic20208651
  "2020-8651 7399_SCENIC_EPBC_REFERRAL_opt_2.pdf"
  "rendered PDF page 40 / Plan 5"
  "Plan maps potential critical Koala habitat through the referral area and labels 23.52 ha habitat to remove."
  "Saunders Havill Group, 1 April 2020"
  "EPBC significant-impact / cumulative-fragmentation / offset consumer"
  "Proponent technical map; later Preliminary Documentation or Commonwealth decision may refine the assessment."

scenicContiguous675 : VisualLandscapeReceipt
scenicContiguous675 = visual-landscape-receipt
  scenic20208651
  "2020-8651 7399_SCENIC_EPBC_REFERRAL_opt_2.pdf"
  "rendered PDF page 41 / Plan 6"
  "Plan depicts Scenic within the same-labelled 675 ha contiguous-landscape carrier used in the Peninsula analysis, north of the Peninsula site position."
  "Saunders Havill Group, 1 April 2020"
  "EPBC cumulative fragmentation / cross-project landscape comparison"
  "Same 675 ha label and visually matching carrier support a same-landscape hypothesis; exact polygon identity should still be checked from source GIS."

record CrossProjectVisualWeld : Set where
  constructor cross-project-visual-weld
  field
    first : VisualLandscapeReceipt
    second : VisualLandscapeReceipt
    boundedInference : String
    remainingPayment : String

open CrossProjectVisualWeld public

scenicPeninsulaSameLandscapeWeld : CrossProjectVisualWeld
scenicPeninsulaSameLandscapeWeld = cross-project-visual-weld
  peninsulaContiguous675
  scenicContiguous675
  "Separate SHG project maps depict Peninsula and Scenic against a common 675 ha contiguous-landscape analysis; this is stronger than manual campaign-map proximity alone."
  "Acquire/compare the underlying GIS geometry and then join Springview 2019/8575 before promoting the result to an exact multi-project intersection or cumulative-effect proposition."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameLabelAutomaticallySameGISPolygon : Set where

data ProponentLandscapeMapIsCommonwealthFinding : Set where

data CriticalKoalaMapAutomaticallyPaysNCA13 : Set where

data VisualContinuityAutomaticallyProvesCumulativeLegalEffect : Set where

data HabitatToRemoveAutomaticallyMeansHabitatAlreadyCleared : Set where

noSameLabelPromotion : SameLabelAutomaticallySameGISPolygon → ⊥
noSameLabelPromotion ()

noAgencyPromotion : ProponentLandscapeMapIsCommonwealthFinding → ⊥
noAgencyPromotion ()

noNCA13Promotion : CriticalKoalaMapAutomaticallyPaysNCA13 → ⊥
noNCA13Promotion ()

noCumulativePromotion : VisualContinuityAutomaticallyProvesCumulativeLegalEffect → ⊥
noCumulativePromotion ()

noClearingPromotion : HabitatToRemoveAutomaticallyMeansHabitatAlreadyCleared → ⊥
noClearingPromotion ()
