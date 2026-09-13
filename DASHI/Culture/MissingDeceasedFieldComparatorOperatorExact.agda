module DASHI.Culture.MissingDeceasedFieldComparatorOperatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Core.ScientificOperatorFamilyExact as O

nunoFieldComparator : O.OperatorFactorisation
nunoFieldComparator = O.operator-factorisation
  "Nuno F. G. Loureiro"
  "DASHI.Physics.Plasma.LoureiroViriatoPlasmoidBidiExact"
  O.fieldComparatorShape
  "reduced plasma state + model parameters -> KREHM/KRMHD/Hermite evolution -> finite plasma observables"
  "The reusable operator is model-state-to-observable comparison; plasma equations remain domain-specific."

ningFieldComparator : O.OperatorFactorisation
ningFieldComparator = O.operator-factorisation
  "Ning Li"
  "DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact"
  O.fieldComparatorShape
  "superconducting/apparatus regime + controls -> precision gravity comparison -> null/residual discriminator"
  "Comparator discipline is reusable; no null result or theoretical model is promoted into a positive anomalous-force claim."

amyFieldComparator : O.OperatorFactorisation
amyFieldComparator = O.operator-factorisation
  "Amy Eskridge"
  "DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact"
  O.fieldComparatorShape
  "programme-level engineered-gravity mechanism claims"
  "Programme-level comparator/null-test decomposition only; no Amy-authored executable science object is paid."

amyFieldComparatorExecutable : Bool
amyFieldComparatorExecutable = false

fieldComparatorFactorisations : List O.OperatorFactorisation
fieldComparatorFactorisations = nunoFieldComparator ∷ ningFieldComparator ∷ amyFieldComparator ∷ []
