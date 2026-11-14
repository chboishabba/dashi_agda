module DASHI.DA51.Atlas where

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_^_)
open import Data.Nat.DivMod using (_/_; _%_)
open import DASHI.DA51.Core

------------------------------------------------------------------------
-- Type 8 data:
-- [level:4][biome:4][status:4][serial:12][reserved:20]
------------------------------------------------------------------------

data Level : Set where
  delta0 sigma1 pi1 pi2 sigma2 lean : Level

-- Keep the code table explicit rather than relying on constructor order.
levelCode : Level → Nat
levelCode delta0 = 0
levelCode pi1    = 1
levelCode sigma1 = 2
levelCode pi2    = 3
levelCode sigma2 = 4
levelCode lean   = 5

levelOfCode : Nat → Maybe Level
levelOfCode 0 = just delta0
levelOfCode 1 = just pi1
levelOfCode 2 = just sigma1
levelOfCode 3 = just pi2
levelOfCode 4 = just sigma2
levelOfCode 5 = just lean
levelOfCode _ = nothing

data Biome : Set where
  moonshineHighlands : Biome
  eisensteinPlains   : Biome
  spectralSea        : Biome
  bridgeMarsh        : Biome
  oggArchipelago     : Biome
  scaffoldFoothills  : Biome
  galleryPeaks       : Biome
  machineWorks       : Biome
  haltingPens        : Biome

biomeCode : Biome → Nat
biomeCode moonshineHighlands = 0
biomeCode eisensteinPlains   = 1
biomeCode spectralSea        = 2
biomeCode bridgeMarsh        = 3
biomeCode oggArchipelago     = 4
biomeCode scaffoldFoothills  = 5
biomeCode galleryPeaks       = 6
biomeCode machineWorks       = 7
biomeCode haltingPens        = 8

biomeOfCode : Nat → Maybe Biome
biomeOfCode 0 = just moonshineHighlands
biomeOfCode 1 = just eisensteinPlains
biomeOfCode 2 = just spectralSea
biomeOfCode 3 = just bridgeMarsh
biomeOfCode 4 = just oggArchipelago
biomeOfCode 5 = just scaffoldFoothills
biomeOfCode 6 = just galleryPeaks
biomeOfCode 7 = just machineWorks
biomeOfCode 8 = just haltingPens
biomeOfCode _ = nothing

data Status : Set where
  openStatus        : Status
  provedTrue        : Status
  provedFalse       : Status
  trueInLiterature  : Status
  falseInLiterature : Status

statusCode : Status → Nat
statusCode openStatus        = 0
statusCode provedTrue        = 1
statusCode provedFalse       = 2
statusCode trueInLiterature  = 3
statusCode falseInLiterature = 4

statusOfCode : Nat → Maybe Status
statusOfCode 0 = just openStatus
statusOfCode 1 = just provedTrue
statusOfCode 2 = just provedFalse
statusOfCode 3 = just trueInLiterature
statusOfCode 4 = just falseInLiterature
statusOfCode _ = nothing

record AtlasCoord : Set where
  constructor coord
  field
    level  : Level
    biome  : Biome
    status : Status
    serial : Nat
open AtlasCoord public

pow20 : Nat
pow20 = 2 ^ 20

pow32 : Nat
pow32 = 2 ^ 32

pow36 : Nat
pow36 = 2 ^ 36

pow40 : Nat
pow40 = 2 ^ 40

dataWord : AtlasCoord → Nat
dataWord c =
  (((levelCode (level c) * 16 + biomeCode (biome c)) * 16 + statusCode (status c))
    * 4096 + serial c % 4096) * pow20

address : AtlasCoord → DA51Address
address c = mkAddr (code atlasEntry) (dataWord c)

levelField : Nat → Nat
levelField d = (d / pow40) % 16

biomeField : Nat → Nat
biomeField d = (d / pow36) % 16

statusField : Nat → Nat
statusField d = (d / pow32) % 16

serialField : Nat → Nat
serialField d = (d / pow20) % 4096

reservedField : Nat → Nat
reservedField d = d % pow20

assemble : Maybe Level → Maybe Biome → Maybe Status → Nat → Maybe AtlasCoord
assemble (just l) (just b) (just s) n = just (coord l b s n)
assemble _ _ _ _ = nothing

decodeData : Nat → Maybe AtlasCoord
decodeData d with reservedField d
... | zero = assemble (levelOfCode (levelField d)) (biomeOfCode (biomeField d))
                    (statusOfCode (statusField d)) (serialField d)
... | suc _ = nothing

-- A canonical atlas decoder checks both the DA51 prefix and the type-8 nibble.
decodeAtlas : DA51Address → Maybe AtlasCoord
decodeAtlas a with prefixOf a | typeOf a
... | 55889 | 8 = decodeData (dataOf a)
... | _     | _ = nothing

-- The wire status is descriptive only.  Proof/security authority lives in
-- the typed producer that attaches evidence to an address, not in this codec.
