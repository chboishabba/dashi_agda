module DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionExact as Obstruction

contractingSurvivorCorrectionBoundPaid :
  Obstruction.InfiniteSurvivorAffineBoundary.contractingSurvivorCorrectionDominancePaid
    Obstruction.canonicalInfiniteSurvivorAffineBoundary
  ≡ 1
contractingSurvivorCorrectionBoundPaid = refl

familyEscapeRefutesInfiniteSurvivorPaid :
  Obstruction.InfiniteSurvivorAffineBoundary.oneContractingCorrectionFitRefutesInfiniteSurvivorPaid
    Obstruction.canonicalInfiniteSurvivorAffineBoundary
  ≡ 1
familyEscapeRefutesInfiniteSurvivorPaid = refl

noUniversalEscapeYet :
  Obstruction.InfiniteSurvivorAffineBoundary.universalContractingCorrectionEscapeProducerPaid
    Obstruction.canonicalInfiniteSurvivorAffineBoundary
  ≡ 0
noUniversalEscapeYet = refl
