module DASHI.Moonshine.OggSSPClimbingGymEmpiricalDiscriminatorTerminalValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Moonshine.OggSSPClimbingGymEmpiricalDiscriminatorTerminalExact as Target

validationDirichletHeldOutNoReplication :
  Target.dirichletHeldOutNoReplication
    Target.canonicalEmpiricalDiscriminatorTerminal
  ≡ true
validationDirichletHeldOutNoReplication = refl

validationAddressBothWindowsNull :
  Target.nativeAddressBothWindowsNonExtreme
    Target.canonicalEmpiricalDiscriminatorTerminal
  ≡ true
validationAddressBothWindowsNull = refl

validationNoMonsterSpecificEmpiricalPromotion :
  Target.monsterSpecificEmpiricalDiscriminatorEstablished
    Target.canonicalEmpiricalDiscriminatorTerminal
  ≡ false
validationNoMonsterSpecificEmpiricalPromotion = refl

validationNoRHPromotion :
  Target.riemannHypothesisEvidenceEstablished
    Target.canonicalEmpiricalDiscriminatorTerminal
  ≡ false
validationNoRHPromotion = refl
