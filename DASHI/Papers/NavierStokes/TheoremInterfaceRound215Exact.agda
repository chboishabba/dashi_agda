module DASHI.Papers.NavierStokes.TheoremInterfaceRound215Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound215Exact as R215

round215PaperComparableFixedBandClosed : Bool
round215PaperComparableFixedBandClosed =
  R215.round215ComparableTwoSidedFixedBandClosed

round215PaperConstantBandAloneInsufficient : Bool
round215PaperConstantBandAloneInsufficient =
  R215.round215ConstantBandAloneInsufficient

round215PaperPositiveThreeClassCompilerClosed : Bool
round215PaperPositiveThreeClassCompilerClosed =
  R215.round215PositiveThreeClassResidualCompilerClosed

round215PaperAllThreeResidualProducersClosed : Bool
round215PaperAllThreeResidualProducersClosed =
  R215.round215AllThreeClassResidualProducersClosed

round215PaperPackageAClosed : Bool
round215PaperPackageAClosed = R215.round215PackageAClosed

round215PaperClayPromotion : Bool
round215PaperClayPromotion = R215.round215ClayPromotion

round215PaperComparableFixedBandClosedIsTrue :
  round215PaperComparableFixedBandClosed ≡ true
round215PaperComparableFixedBandClosedIsTrue = refl

round215PaperConstantBandAloneInsufficientIsTrue :
  round215PaperConstantBandAloneInsufficient ≡ true
round215PaperConstantBandAloneInsufficientIsTrue = refl

round215PaperAllThreeResidualProducersClosedIsFalse :
  round215PaperAllThreeResidualProducersClosed ≡ false
round215PaperAllThreeResidualProducersClosedIsFalse = refl

round215PaperPackageAClosedIsFalse : round215PaperPackageAClosed ≡ false
round215PaperPackageAClosedIsFalse = refl

round215PaperClayPromotionIsFalse : round215PaperClayPromotion ≡ false
round215PaperClayPromotionIsFalse = refl
