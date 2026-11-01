module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractExact as Contract

contractKeepsRequirednessSeparate :
  Contract.requirednessSeparateFromSalience Contract.canonicalFiniteRequirementParetoContract ≡ true
contractKeepsRequirednessSeparate = refl

contractAllowsParetoMultiplicity :
  Contract.frontierMayContainMultipleCells Contract.canonicalFiniteRequirementParetoContract ≡ true
contractAllowsParetoMultiplicity = refl
