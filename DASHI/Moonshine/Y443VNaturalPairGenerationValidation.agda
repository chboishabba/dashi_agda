module DASHI.Moonshine.Y443VNaturalPairGenerationValidation where

------------------------------------------------------------------------
-- Focused golden root: finite Y443 relators and constructive literal
-- V-natural action transport; keep the Suzuki 12 distinct from Y443 12.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y443
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDTracePowerExact as JMD
import DASHI.Moonshine.Y443Monster3BTwelveDisjointExact as H3
import DASHI.Moonshine.Y443ArmSwapOrbitMaxCutExact as Orbit
import DASHI.Moonshine.Y443Relator72IndexedBidiExact as Indexed
import DASHI.Moonshine.Y443Nonary72EquivarianceNoGoExact as NoGo
import DASHI.Moonshine.Monster3BNormalizerBridge as N3B

coxeterTwelveMatchesSuzukiDegreeNumerically :
  Y443.length Y443.nodes ≡ N3B.naturalSuzukiDegree
coxeterTwelveMatchesSuzukiDegreeNumerically = refl

coxeterTwelveIsNotSuzukiCoordinateIdentity :
  Y443.coxeterInvolutionAlphabet ≡ Y443.suzukiDegreeTwelve → ⊥
coxeterTwelveIsNotSuzukiCoordinateIdentity =
  Y443.distinctTwelveRoles

y443RelatorCountIsEighty :
  Y443.length Y443.monsterRelators ≡ 80
y443RelatorCountIsEighty = Y443.monsterRelatorCount

y443WrittenLengthIsFourSixtyThree :
  Y443.wordLengthSum Y443.monsterRelators ≡ 463
y443WrittenLengthIsFourSixtyThree = Y443.monsterWrittenLength
