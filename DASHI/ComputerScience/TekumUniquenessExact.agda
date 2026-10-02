module DASHI.ComputerScience.TekumUniquenessExact where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.ComputerScience.TekumFormalPropertiesExact as Formal

------------------------------------------------------------------------
-- Proposition 2 owner: any concrete decoder that supplies the source interval
-- separation proof can inhabit this exact injectivity contract.

TekumInjectivityWitness = Formal.TekumInjectivityWitness
