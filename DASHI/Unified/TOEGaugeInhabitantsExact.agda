module DASHI.Unified.TOEGaugeInhabitantsExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (refl)

import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants
open Inhabitants.FormalInhabitantReceipt

agda1164HodgeCrossInhabitant : Inhabitants.FormalInhabitantReceipt
agda1164HodgeCrossInhabitant =
  record
    { prover = "Agda"
    ; repository = "chboishabba/dashi_agda"
    ; pullRequest = 1164
    ; headCommit = "043a55e66b67a71d52612382d7d665e8ec8f8122"
    ; moduleName = "DASHI.Physics.Foundations.R3HodgeCrossExact"
    ; declaration = "hodgeWedgeEqualsCross"
    ; propositionScope =
        "On the concrete R3/SU2 Lie-algebra carrier, Hodge star of the explicit bivector wedge equals the right-hand cross product; the same owner proves the repository normalization [u,v]=2(u cross v)."
    ; authority = Inhabitants.importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

agda1164U1SU2TorusInhabitant : Inhabitants.FormalInhabitantReceipt
agda1164U1SU2TorusInhabitant =
  record
    { prover = "Agda"
    ; repository = "chboishabba/dashi_agda"
    ; pullRequest = 1164
    ; headCommit = "043a55e66b67a71d52612382d7d665e8ec8f8122"
    ; moduleName = "DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact"
    ; declaration = "includePreservesMultiply"
    ; propositionScope =
        "A literal unit-circle U1 group is constructed inside the concrete unit-quaternion SU2 and its inclusion preserves multiplication, inversion and identity."
    ; authority = Inhabitants.importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

agda1165BrownMaclayStressInhabitant : Inhabitants.FormalInhabitantReceipt
agda1165BrownMaclayStressInhabitant =
  record
    { prover = "Agda"
    ; repository = "chboishabba/dashi_agda"
    ; pullRequest = 1165
    ; headCommit = "64c8d33320a8e313064a565068ae399566b4de23"
    ; moduleName = "DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact"
    ; declaration = "canonicalBrownMaclayNormalizedStressWitness"
    ; propositionScope =
        "Source-bounded ideal parallel-plate electromagnetic stress witness with normalized rho=-1, tangential pressures +1,+1, normal pressure -3; the same owner derives T(k,k)=-4w for normal squared weight w."
    ; authority = Inhabitants.importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

record GaugeFormalInhabitantBundle : Set where
  field
    hodgeCross : Inhabitants.FormalInhabitantReceipt
    u1InsideSU2 : Inhabitants.FormalInhabitantReceipt
    brownMaclayStress : Inhabitants.FormalInhabitantReceipt

canonicalGaugeFormalInhabitantBundle : GaugeFormalInhabitantBundle
canonicalGaugeFormalInhabitantBundle =
  record
    { hodgeCross = agda1164HodgeCrossInhabitant
    ; u1InsideSU2 = agda1164U1SU2TorusInhabitant
    ; brownMaclayStress = agda1165BrownMaclayStressInhabitant
    }
