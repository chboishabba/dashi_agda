module DASHI.Core.ContactHamiltonian where

------------------------------------------------------------------------
-- Generic residual-energy surface.
--
-- Different domains instantiate this with different residuals and energy
-- notions: chi2/dof in HEP, rollout error in world models, enactment gap
-- in education, or mismatch/instability pressure in cognition.
------------------------------------------------------------------------

record ContactHamiltonian : Set₁ where
  constructor contactHamiltonian
  field
    Residual         : Set
    Energy           : Set
    Hamiltonian      : Residual → Energy
    Pressure         : Energy → Set
    AuthorityPenalty : Energy → Set

open ContactHamiltonian public
