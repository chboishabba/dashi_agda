module DASHI.Companions.CertifiedMoonshineCategoricalBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Moonshine.MonsterCharacterTableExact as MCT
import DASHI.Moonshine.JCoefficientCharacterBridge as JCB

------------------------------------------------------------------------
-- The two lanes meet only through a named, separately supplied lift.  This
-- module intentionally provides no inhabitant of such a lift.

record CertifiedMoonshineStatement : Set where
  field
    firstCoefficientBridge : JCB.FirstMoonshineCoefficientBridge
    modularAuthorityReading : String

record MaassToMonsterBridge : Set₁ where
  field
    bridgeReading : String
    -- A specific theta/Borcherds/harmonic-Maaß/trace-formula bridge must
    -- supply its own domain, codomain, and proof obligations.
    authorityBacked : Bool

directMaassToMonsterAvailable : Bool
directMaassToMonsterAvailable = false

