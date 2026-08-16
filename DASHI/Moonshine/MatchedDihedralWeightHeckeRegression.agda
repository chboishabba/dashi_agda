module DASHI.Moonshine.MatchedDihedralWeightHeckeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.MatchedDihedralWeightHeckeQuotientExact as Weight

j4FirstPair : Matched.PairIndex 4
j4FirstPair = Matched.firstPair {j = 3}

j4PositiveNegativeSameSector :
  Weight.weightSector (Weight.positiveWeight j4FirstPair)
  ≡ Weight.weightSector (Weight.negativeWeight j4FirstPair)
j4PositiveNegativeSameSector =
  Weight.oppositeWeightsSameSector j4FirstPair

j4FirstPairIsDoublet :
  Weight.weightSector (Weight.positiveWeight j4FirstPair)
  ≡ Matched.pairedDoublet j4FirstPair
j4FirstPairIsDoublet = refl

j4CentralIsSelectedSinglet :
  Weight.weightSector (Weight.centralWeight {j = 4})
  ≡ Matched.selectedSinglet
j4CentralIsSelectedSinglet = refl

j4DoubletRepresentativeIsPositive :
  Weight.sectorRepresentative (Matched.pairedDoublet j4FirstPair)
  ≡ Weight.positiveWeight j4FirstPair
j4DoubletRepresentativeIsPositive =
  Weight.positiveRepresentativeOfDoublet j4FirstPair
