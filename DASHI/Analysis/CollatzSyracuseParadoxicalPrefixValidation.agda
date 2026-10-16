module DASHI.Analysis.CollatzSyracuseParadoxicalPrefixValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox

sameOddCountInsufficient :
  Paradox.ParadoxicalPrefixBoundary.sameOddCountDoesNotDetermineAffineCorrection
    Paradox.canonicalParadoxicalPrefixBoundary
  ≡ 1
sameOddCountInsufficient = refl

contractingCorrectionCompilerPaid :
  Paradox.ParadoxicalPrefixBoundary.contractingCorrectionFitImpliesLiteralDescent
    Paradox.canonicalParadoxicalPrefixBoundary
  ≡ 1
contractingCorrectionCompilerPaid = refl

paradoxicalDoesNotSolveUniversalTail :
  Paradox.ParadoxicalPrefixBoundary.paradoxicalClassificationAutomaticallyEliminatesAllResidualStarts
    Paradox.canonicalParadoxicalPrefixBoundary
  ≡ 0
paradoxicalDoesNotSolveUniversalTail = refl
