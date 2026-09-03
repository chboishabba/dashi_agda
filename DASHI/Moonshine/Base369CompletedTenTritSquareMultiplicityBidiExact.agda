module DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact where

------------------------------------------------------------------------
-- SEMANTIC REFINEMENT OF THE BASE369 90-CARRIER
--
-- Replace the anonymous address product Fin 10 x Fin 9 by the already-owned
-- Base369 carriers
--
--   CoarseChannel x TritSquare
--   = (T^2 + {completion j}) x T^2.
--
-- Thus the numerical identity 90 = 10 x 9 becomes the typed carrier
--
--   90 ~= Completed10 x T^2.
--
-- The maps below are explicit finite charts.  They do not identify Z/9 with
-- F_3^2 as an algebra, and they do not identify the actual Monster Fin 90
-- action until an intertwining receipt is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual

------------------------------------------------------------------------
-- 1. Fin 10 <-> completed Base369 coarse carrier T^2 + {j}.
------------------------------------------------------------------------

fin10ToCoarse : Pointed.Fine10 → Harmonic.CoarseChannel
fin10ToCoarse zero = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)
fin10ToCoarse (suc zero) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)
fin10ToCoarse (suc (suc zero)) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)
fin10ToCoarse (suc (suc (suc zero))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)
fin10ToCoarse (suc (suc (suc (suc zero)))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)
fin10ToCoarse (suc (suc (suc (suc (suc zero))))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)
fin10ToCoarse (suc (suc (suc (suc (suc (suc zero)))))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)
fin10ToCoarse (suc (suc (suc (suc (suc (suc (suc zero))))))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)
fin10ToCoarse (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)
fin10ToCoarse (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = Harmonic.completionJ

coarseToFin10 : Harmonic.CoarseChannel → Pointed.Fine10
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = zero
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = suc zero
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = suc (suc zero)
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = suc (suc (suc zero))
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = suc (suc (suc (suc zero)))
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = suc (suc (suc (suc (suc zero))))
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = suc (suc (suc (suc (suc (suc zero)))))
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = suc (suc (suc (suc (suc (suc (suc zero))))))
coarseToFin10 (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
coarseToFin10 Harmonic.completionJ = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

coarseAfterFin10 : (index : Pointed.Fine10) → coarseToFin10 (fin10ToCoarse index) ≡ index
coarseAfterFin10 zero = refl
coarseAfterFin10 (suc zero) = refl
coarseAfterFin10 (suc (suc zero)) = refl
coarseAfterFin10 (suc (suc (suc zero))) = refl
coarseAfterFin10 (suc (suc (suc (suc zero)))) = refl
coarseAfterFin10 (suc (suc (suc (suc (suc zero))))) = refl
coarseAfterFin10 (suc (suc (suc (suc (suc (suc zero)))))) = refl
coarseAfterFin10 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
coarseAfterFin10 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
coarseAfterFin10 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

fin10AfterCoarse : (coarse : Harmonic.CoarseChannel) → fin10ToCoarse (coarseToFin10 coarse) ≡ coarse
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = refl
fin10AfterCoarse (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = refl
fin10AfterCoarse Harmonic.completionJ = refl

------------------------------------------------------------------------
-- 2. Fin 9 <-> the literal two-trit square T^2.
--    Ordering matches Base369NonaryTritSquareExact's nonary chart.
------------------------------------------------------------------------

fin9ToTritSquare : Pointed.SecondarySheet9 → Square.TritSquare
fin9ToTritSquare zero = Square.tritSquare SSP.sspZero SSP.sspZero
fin9ToTritSquare (suc zero) = Square.tritSquare SSP.sspZero SSP.sspPosOne
fin9ToTritSquare (suc (suc zero)) = Square.tritSquare SSP.sspZero SSP.sspNegOne
fin9ToTritSquare (suc (suc (suc zero))) = Square.tritSquare SSP.sspPosOne SSP.sspZero
fin9ToTritSquare (suc (suc (suc (suc zero)))) = Square.tritSquare SSP.sspPosOne SSP.sspPosOne
fin9ToTritSquare (suc (suc (suc (suc (suc zero))))) = Square.tritSquare SSP.sspPosOne SSP.sspNegOne
fin9ToTritSquare (suc (suc (suc (suc (suc (suc zero)))))) = Square.tritSquare SSP.sspNegOne SSP.sspZero
fin9ToTritSquare (suc (suc (suc (suc (suc (suc (suc zero))))))) = Square.tritSquare SSP.sspNegOne SSP.sspPosOne
fin9ToTritSquare (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Square.tritSquare SSP.sspNegOne SSP.sspNegOne

tritSquareToFin9 : Square.TritSquare → Pointed.SecondarySheet9
tritSquareToFin9 (Square.tritSquare SSP.sspZero SSP.sspZero) = zero
tritSquareToFin9 (Square.tritSquare SSP.sspZero SSP.sspPosOne) = suc zero
tritSquareToFin9 (Square.tritSquare SSP.sspZero SSP.sspNegOne) = suc (suc zero)
tritSquareToFin9 (Square.tritSquare SSP.sspPosOne SSP.sspZero) = suc (suc (suc zero))
tritSquareToFin9 (Square.tritSquare SSP.sspPosOne SSP.sspPosOne) = suc (suc (suc (suc zero)))
tritSquareToFin9 (Square.tritSquare SSP.sspPosOne SSP.sspNegOne) = suc (suc (suc (suc (suc zero))))
tritSquareToFin9 (Square.tritSquare SSP.sspNegOne SSP.sspZero) = suc (suc (suc (suc (suc (suc zero)))))
tritSquareToFin9 (Square.tritSquare SSP.sspNegOne SSP.sspPosOne) = suc (suc (suc (suc (suc (suc (suc zero))))))
tritSquareToFin9 (Square.tritSquare SSP.sspNegOne SSP.sspNegOne) = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

tritSquareAfterFin9 : (index : Pointed.SecondarySheet9) → tritSquareToFin9 (fin9ToTritSquare index) ≡ index
tritSquareAfterFin9 zero = refl
tritSquareAfterFin9 (suc zero) = refl
tritSquareAfterFin9 (suc (suc zero)) = refl
tritSquareAfterFin9 (suc (suc (suc zero))) = refl
tritSquareAfterFin9 (suc (suc (suc (suc zero)))) = refl
tritSquareAfterFin9 (suc (suc (suc (suc (suc zero))))) = refl
tritSquareAfterFin9 (suc (suc (suc (suc (suc (suc zero)))))) = refl
tritSquareAfterFin9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
tritSquareAfterFin9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl

fin9AfterTritSquare : (square : Square.TritSquare) → fin9ToTritSquare (tritSquareToFin9 square) ≡ square
fin9AfterTritSquare (Square.tritSquare SSP.sspZero SSP.sspZero) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspZero SSP.sspPosOne) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspZero SSP.sspNegOne) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspPosOne SSP.sspZero) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspPosOne SSP.sspPosOne) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspPosOne SSP.sspNegOne) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspNegOne SSP.sspZero) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspNegOne SSP.sspPosOne) = refl
fin9AfterTritSquare (Square.tritSquare SSP.sspNegOne SSP.sspNegOne) = refl

------------------------------------------------------------------------
-- 3. Complete typed 90 carrier.
------------------------------------------------------------------------

CompletedTenTritSquare : Set
CompletedTenTritSquare = Harmonic.CoarseChannel × Square.TritSquare

toCompletedTenTritSquare : Ninety.TenByNineMultiplicity → CompletedTenTritSquare
toCompletedTenTritSquare (fine , sheet) = fin10ToCoarse fine , fin9ToTritSquare sheet

fromCompletedTenTritSquare : CompletedTenTritSquare → Ninety.TenByNineMultiplicity
fromCompletedTenTritSquare (coarse , square) = coarseToFin10 coarse , tritSquareToFin9 square

fromAfterToCompleted :
  (state : Ninety.TenByNineMultiplicity) →
  fromCompletedTenTritSquare (toCompletedTenTritSquare state) ≡ state
fromAfterToCompleted (fine , sheet)
  rewrite coarseAfterFin10 fine | tritSquareAfterFin9 sheet = refl

toAfterFromCompleted :
  (state : CompletedTenTritSquare) →
  toCompletedTenTritSquare (fromCompletedTenTritSquare state) ≡ state
toAfterFromCompleted (coarse , square)
  rewrite fin10AfterCoarse coarse | fin9AfterTritSquare square = refl

------------------------------------------------------------------------
-- 4. Same-action promotion from the already-live Fin90 <-> 10x9 attachment.
------------------------------------------------------------------------

record ActualMultiplicityCompletedTenTritSquareAttachment
    {source : Action.ActualMonster3BActionRecognition}
    (inertiaAttachment : Actual.ActualMultiplicityInertiaAttachment source)
    : Set₁ where
  field
    tenByNineAttachment : Ninety.ActualMultiplicityTenByNineAttachment inertiaAttachment
    completedAct :
      Actual.MultiplicityInertia inertiaAttachment →
      CompletedTenTritSquare → CompletedTenTritSquare
    completedChartIntertwines :
      (inertia : Actual.MultiplicityInertia inertiaAttachment) →
      (surface : Ninety.TenByNineMultiplicity) →
      toCompletedTenTritSquare
        (Ninety.tenByNineAct tenByNineAttachment inertia surface)
      ≡ completedAct inertia (toCompletedTenTritSquare surface)
open ActualMultiplicityCompletedTenTritSquareAttachment public

record CompletedTenTritSquareBoundary : Set where
  constructor completedTenTritSquareBoundary
  field
    completedTenCarrierIsTritSquarePlusJ : Bool
    secondaryNineIsLiteralTritSquare : Bool
    tenByNineToCompletedTenTritSquareIsTwoSided : Bool
    actualFin90StillRequiresRecognition : Bool
    sameActualActionStillRequired : Bool
    carrierChartIdentifiesZ9WithF3SquaredAsAlgebra : Bool

canonicalCompletedTenTritSquareBoundary : CompletedTenTritSquareBoundary
canonicalCompletedTenTritSquareBoundary =
  completedTenTritSquareBoundary true true true true true false
