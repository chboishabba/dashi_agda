module DASHI.DA51.Core where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_^_)
open import Data.Nat.DivMod using (_/_; _%_)

------------------------------------------------------------------------
-- Canonical 0xDA51 wire ABI
--
-- [prefix:16][type:4][data:44]
--
-- The numeric assignments 0..7 are historical and frozen.  Type 8 is the
-- additive theory-atlas address type.
------------------------------------------------------------------------

prefixVal : Nat
prefixVal = 55889  -- 0xDA51

data AddrType : Set where
  monsterWalk     : AddrType
  astNode         : AddrType
  monsterProtocol : AddrType
  nestedCID       : AddrType
  harmonicPath    : AddrType
  shardID         : AddrType
  eigenspaceAddr  : AddrType
  hauptmodul      : AddrType
  atlasEntry      : AddrType

code : AddrType → Nat
code monsterWalk     = 0
code astNode         = 1
code monsterProtocol = 2
code nestedCID       = 3
code harmonicPath    = 4
code shardID         = 5
code eigenspaceAddr  = 6
code hauptmodul      = 7
code atlasEntry      = 8

ofCode : Nat → Maybe AddrType
ofCode 0 = just monsterWalk
ofCode 1 = just astNode
ofCode 2 = just monsterProtocol
ofCode 3 = just nestedCID
ofCode 4 = just harmonicPath
ofCode 5 = just shardID
ofCode 6 = just eigenspaceAddr
ofCode 7 = just hauptmodul
ofCode 8 = just atlasEntry
ofCode _ = nothing

ofCode-code : (t : AddrType) → ofCode (code t) ≡ just t
ofCode-code monsterWalk     = refl
ofCode-code astNode         = refl
ofCode-code monsterProtocol = refl
ofCode-code nestedCID       = refl
ofCode-code harmonicPath    = refl
ofCode-code shardID         = refl
ofCode-code eigenspaceAddr  = refl
ofCode-code hauptmodul      = refl
ofCode-code atlasEntry      = refl

-- A typed DA51 identity.  This is an address only: it carries no proof,
-- literature, ZK, or security authority by itself.
record DA51Address : Set where
  constructor addr
  field
    raw : Nat
open DA51Address public

pow44 : Nat
pow44 = 2 ^ 44

pow48 : Nat
pow48 = 2 ^ 48

mkAddr : Nat → Nat → DA51Address
mkAddr t d = addr (prefixVal * pow48 + (t % 16) * pow44 + d % pow44)

prefixOf : DA51Address → Nat
prefixOf a = raw a / pow48

typeOf : DA51Address → Nat
typeOf a = (raw a / pow44) % 16

dataOf : DA51Address → Nat
dataOf a = raw a % pow44

knownType : DA51Address → Maybe AddrType
knownType a = ofCode (typeOf a)

-- Header constants kept explicit for external fixtures.
dataMask : Nat
dataMask = 17592186044415  -- 0x00000FFFFFFFFFFF

prefixShift : Nat
prefixShift = 48

typeShift : Nat
typeShift = 44

-- Simple computation fixtures pin the historical registry.
type0-fixture : code monsterWalk ≡ 0
type0-fixture = refl

type7-fixture : code hauptmodul ≡ 7
type7-fixture = refl

type8-fixture : code atlasEntry ≡ 8
type8-fixture = refl
