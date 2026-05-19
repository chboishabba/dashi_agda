module DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_)

open import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATJ
  using
    ( trajectoryGen
    ; trajectory-π-mdl-max-constant
    ; trajectoryPrimeDistinct01
    ; trajectoryPrimeDistinct02
    ; trajectoryPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractBalancedComposedFamily as SBCF
  using
    ( balancedComposedGen
    ; balancedComposed-π-mdl-max-constant
    ; balancedComposedPrimeDistinct01
    ; balancedComposedPrimeDistinct02
    ; balancedComposedPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractComposedFamily as SCF
  using
    ( composedGen
    ; composed-π-mdl-max-constant
    ; composedPrimeDistinct01
    ; composedPrimeDistinct02
    ; composedPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractStateFamily as SCSF
  using
    ( ShiftContractStateFamily
    ; canonicalFamilyAt
    )
open import DASHI.Physics.Closure.ShiftContractParametricTriadicFamily as SPTF
  using (width1; width2; width3)
open import DASHI.Physics.Closure.ShiftContractTriadic3CycleInstance as ST3
  using
    ( cycleGen
    ; balancedπ-constant
    ; balancedPrimeDistinct01
    ; balancedPrimeDistinct02
    ; balancedPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1)

------------------------------------------------------------------------
-- Normalized generator-class surface above the finite witness modules.
--
-- This packages the successful same-carrier 3-state prefixes from:
-- - explicit cyclic families,
-- - the concrete balanced 3-cycle,
-- - the composed dense branch,
-- - the composed balanced branch,
-- - the first live anchored trajectory.
--
-- The goal is not to hide their differences, but to let subsequent search and
-- theorem code quantify over one theorem-bearing generator interface.

data GeneratorClass : Set where
  explicitWidth1 explicitWidth2 explicitWidth3 : GeneratorClass
  balancedCycle : GeneratorClass
  denseComposed : GeneratorClass
  balancedComposed : GeneratorClass
  anchoredTrajectory : GeneratorClass

familyAt : GeneratorClass → ShiftContractStateFamily TriadicIndex
familyAt explicitWidth1 = canonicalFamilyAt width1
familyAt explicitWidth2 = canonicalFamilyAt width2
familyAt explicitWidth3 = canonicalFamilyAt width3
familyAt balancedCycle =
  record
    { gen = cycleGen
    ; sameπ = balancedπ-constant
    ; supportWidth = 3
    ; nontrivialPrimeImage = i0 , (i1 , balancedPrimeDistinct01)
    }
familyAt denseComposed =
  record
    { gen = composedGen
    ; sameπ = composed-π-mdl-max-constant
    ; supportWidth = 3
    ; nontrivialPrimeImage = i0 , (i1 , composedPrimeDistinct01)
    }
familyAt balancedComposed =
  record
    { gen = balancedComposedGen
    ; sameπ = balancedComposed-π-mdl-max-constant
    ; supportWidth = 3
    ; nontrivialPrimeImage = i0 , (i1 , balancedComposedPrimeDistinct01)
    }
familyAt anchoredTrajectory =
  record
    { gen = trajectoryGen
    ; sameπ = trajectory-π-mdl-max-constant
    ; supportWidth = 2
    ; nontrivialPrimeImage = i0 , (i1 , trajectoryPrimeDistinct01)
    }

record ShiftContractGeneratorFamilySchema : Set₂ where
  field
    family : GeneratorClass → ShiftContractStateFamily TriadicIndex

canonicalShiftContractGeneratorFamilySchema :
  ShiftContractGeneratorFamilySchema
canonicalShiftContractGeneratorFamilySchema =
  record
    { family = familyAt
    }

open ShiftContractGeneratorFamilySchema public
