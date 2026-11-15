module DASHI.DA51.Fixtures where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import DASHI.DA51.Core
open import DASHI.DA51.Atlas

------------------------------------------------------------------------
-- Cross-language golden fixtures.
-- Decimal RHS values are the unsigned-64 interpretations of the exact hex
-- addresses shown in comments.
------------------------------------------------------------------------

c00 : AtlasCoord
c00 = coord delta0 moonshineHighlands provedTrue 0
c01 : AtlasCoord
c01 = coord delta0 moonshineHighlands provedTrue 1
c02 : AtlasCoord
c02 = coord delta0 moonshineHighlands provedTrue 2
c03 : AtlasCoord
c03 = coord delta0 haltingPens provedTrue 3
c04 : AtlasCoord
c04 = coord pi1 haltingPens openStatus 4
c05 : AtlasCoord
c05 = coord pi1 eisensteinPlains provedTrue 5
c06 : AtlasCoord
c06 = coord pi1 bridgeMarsh openStatus 6
c07 : AtlasCoord
c07 = coord pi1 bridgeMarsh falseInLiterature 7
c08 : AtlasCoord
c08 = coord pi2 eisensteinPlains provedTrue 8
c09 : AtlasCoord
c09 = coord pi2 haltingPens openStatus 9
c10 : AtlasCoord
c10 = coord lean bridgeMarsh openStatus 10
c11 : AtlasCoord
c11 = coord lean bridgeMarsh openStatus 11
c12 : AtlasCoord
c12 = coord lean spectralSea openStatus 12
c13 : AtlasCoord
c13 = coord lean eisensteinPlains provedTrue 13
c14 : AtlasCoord
c14 = coord lean eisensteinPlains provedTrue 14
c15 : AtlasCoord
c15 = coord lean spectralSea provedTrue 15
c16 : AtlasCoord
c16 = coord lean spectralSea provedTrue 16
c17 : AtlasCoord
c17 = coord lean spectralSea provedTrue 17
c18 : AtlasCoord
c18 = coord lean moonshineHighlands provedTrue 18
c19 : AtlasCoord
c19 = coord lean moonshineHighlands provedTrue 19
c20 : AtlasCoord
c20 = coord lean moonshineHighlands provedTrue 20
c21 : AtlasCoord
c21 = coord lean moonshineHighlands trueInLiterature 21
c22 : AtlasCoord
c22 = coord lean moonshineHighlands trueInLiterature 22

-- 0xDA51800100000000
f00 : raw (address c00) ≡ 15731495715165175808
f00 = refl
-- 0xDA51800100100000
f01 : raw (address c01) ≡ 15731495715166224384
f01 = refl
-- 0xDA51800100200000
f02 : raw (address c02) ≡ 15731495715167272960
f02 = refl
-- 0xDA51808100300000
f03 : raw (address c03) ≡ 15731496264924135424
f03 = refl
-- 0xDA51818000400000
f04 : raw (address c04) ≡ 15731497360141844480
f04 = refl
-- 0xDA51811100500000
f05 : raw (address c05) ≡ 15731496883401523200
f05 = refl
-- 0xDA51813000600000
f06 : raw (address c06) ≡ 15731497016546557952
f06 = refl
-- 0xDA51813400700000
f07 : raw (address c07) ≡ 15731497033727475712
f07 = refl
-- 0xDA51831100800000
f08 : raw (address c08) ≡ 15731499082427924480
f08 = refl
-- 0xDA51838000900000
f09 : raw (address c09) ≡ 15731499559170342912
f09 = refl
-- 0xDA51853000A00000
f10 : raw (address c10) ≡ 15731501414597263360
f10 = refl
-- 0xDA51853000B00000
f11 : raw (address c11) ≡ 15731501414598311936
f11 = refl
-- 0xDA51852000C00000
f12 : raw (address c12) ≡ 15731501345879883776
f12 = refl
-- 0xDA51851100D00000
f13 : raw (address c13) ≡ 15731501281456422912
f13 = refl
-- 0xDA51851100E00000
f14 : raw (address c14) ≡ 15731501281457471488
f14 = refl
-- 0xDA51852100F00000
f15 : raw (address c15) ≡ 15731501350177996800
f15 = refl
-- 0xDA51852101000000
f16 : raw (address c16) ≡ 15731501350179045376
f16 = refl
-- 0xDA51852101100000
f17 : raw (address c17) ≡ 15731501350180093952
f17 = refl
-- 0xDA51850101200000
f18 : raw (address c18) ≡ 15731501212742189056
f18 = refl
-- 0xDA51850101300000
f19 : raw (address c19) ≡ 15731501212743237632
f19 = refl
-- 0xDA51850101400000
f20 : raw (address c20) ≡ 15731501212744286208
f20 = refl
-- 0xDA51850301500000
f21 : raw (address c21) ≡ 15731501221335269376
f21 = refl
-- 0xDA51850301600000
f22 : raw (address c22) ≡ 15731501221336317952
f22 = refl

-- Representative round-trip fixtures.  The other entries share the same codec.
d00 : decodeAtlas (address c00) ≡ just c00
d00 = refl

d22 : decodeAtlas (address c22) ≡ just c22
d22 = refl

-- Reserved bits are rejected: 0xDA51800100000001.
reserved-rejected : decodeAtlas (addr 15731495715165175809) ≡ nothing
reserved-rejected = refl
