module DASHI.Arithmetic.TwinPrimeTernary270SurvivorCoverageExact where

------------------------------------------------------------------------
-- EXACT FINITE SURVIVOR COVERAGE AT MODULUS 270
--
-- REUSE: Base369Ternary27HypervoxelFabricGeometryExact owns typed
-- x/y/z trits; TwinPrimeTernary270AffineCRTCodecExact owns the
-- injective affine code and certified forward sieve proof.
-- CertifiedPrimePairModulusExact owns actual arithmetic local guards.
-- NEW: reverse coverage of EVERY residue in Fin 270 under those
-- guards, using a finite proof table with 270 computational cases.
--
-- This is a 3 x 3 x 3 cube, not 27 untyped labels. The actual
-- arithmetic projections are 1 residue mod 2, 9 residues mod 27
-- from y/z, and 3 residues mod 5 from x. These are NOT three
-- independent prime-modulus axes. The map is a finite CRT-wheel
-- bijection, NOT a twin-prime distribution theorem or Monster/3B
-- same-object claim. Prior Conway/Guy, Ibrahim and mathematics
-- authorship remains with the original owners.
--
-- Source-written, Agda kernel-pending. No CI assertion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Base as Fin
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; trans; sym; subst)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Arithmetic.TwinPrimeTernary270AffineCRTCodecExact as Codec
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact as Composite
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import Data.Nat.Primality as NatPrime

-- The exact same guards used by the certified 2/3/5 sieve.
Wheel270Survives : Nat → Set
Wheel270Survives n =
  ((n % 2 ≢ 0) × ((n + 2) % 2 ≢ 0)) ×
  (((n % 3 ≢ 0) × ((n + 2) % 3 ≢ 0)) ×
    (((n % 5 ≢ 0) × ((n + 2) % 5 ≢ 0)) × ⊤))

Cover : Nat → Set
Cover n = Wheel270Survives n →
  Σ Geometry.Ternary27Point (λ p → Codec.cubeToWheel270 p ≡ n)

reject2L : (n : Nat) → n % 2 ≡ 0 → Cover n
reject2L n eq (p2 , _) = ⊥-elim (proj₁ p2 eq)

reject2R : (n : Nat) → (n + 2) % 2 ≡ 0 → Cover n
reject2R n eq (p2 , _) = ⊥-elim (proj₂ p2 eq)

reject3L : (n : Nat) → n % 3 ≡ 0 → Cover n
reject3L n eq (_ , (p3 , _)) = ⊥-elim (proj₁ p3 eq)

reject3R : (n : Nat) → (n + 2) % 3 ≡ 0 → Cover n
reject3R n eq (_ , (p3 , _)) = ⊥-elim (proj₂ p3 eq)

reject5L : (n : Nat) → n % 5 ≡ 0 → Cover n
reject5L n eq (_ , (_ , (p5 , _))) =
  ⊥-elim (proj₁ p5 eq)

reject5R : (n : Nat) → (n + 2) % 5 ≡ 0 → Cover n
reject5R n eq (_ , (_ , (p5 , _))) =
  ⊥-elim (proj₂ p5 eq)

-- A finite All over the bounded Nat segment [start,start+length).
-- The bounded segment is indexed by Fin, NOT an assumed universal
-- coverage postulate or an unchecked Boolean survey.
AllFrom : Nat → Nat → (Nat → Set) → Set
AllFrom start zero P = ⊤
AllFrom start (suc size) P =
  P start × AllFrom (suc start) size P

shift : ∀ {n} → Nat → Fin n → Nat
shift start Fin.zero = start
shift start (Fin.suc i) = shift (suc start) i

allAt : ∀ {P : Nat → Set} {n : Nat} →
  (start : Nat) → AllFrom start n P →
  (i : Fin n) → P (shift start i)
allAt {n = suc n} start (head , tail) Fin.zero = head
allAt {n = suc n} start (head , tail) (Fin.suc i) =
  allAt (suc start) tail i

shiftSuc : ∀ {n} (start : Nat) (i : Fin n) →
  shift (suc start) i ≡ suc (shift start i)
shiftSuc start Fin.zero = refl
shiftSuc start (Fin.suc i) = shiftSuc (suc start) i

shiftZero : ∀ {n} (i : Fin n) → shift 0 i ≡ Fin.toℕ i
shiftZero Fin.zero = refl
shiftZero (Fin.suc i) =
  trans (shiftSuc 0 i) (cong suc (shiftZero i))

-- Cases are computed with stdlib Nat mod and the existing affine
-- encoder. Each surviving case returns the FULL typed x/y/z point.
-- Every other case carries a concrete failed prime-modulus guard.
case0 : Cover 0
case0 = reject2L 0 refl

case1 : Cover 1
case1 = reject3R 1 refl

case2 : Cover 2
case2 = reject2L 2 refl

case3 : Cover 3
case3 = reject3L 3 refl

case4 : Cover 4
case4 = reject2L 4 refl

case5 : Cover 5
case5 = reject5L 5 refl

case6 : Cover 6
case6 = reject2L 6 refl

case7 : Cover 7
case7 = reject3R 7 refl

case8 : Cover 8
case8 = reject2L 8 refl

case9 : Cover 9
case9 = reject3L 9 refl

case10 : Cover 10
case10 = reject2L 10 refl

case11 : Cover 11
case11 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne , refl)

case12 : Cover 12
case12 = reject2L 12 refl

case13 : Cover 13
case13 = reject3R 13 refl

case14 : Cover 14
case14 = reject2L 14 refl

case15 : Cover 15
case15 = reject3L 15 refl

case16 : Cover 16
case16 = reject2L 16 refl

case17 : Cover 17
case17 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne , refl)

case18 : Cover 18
case18 = reject2L 18 refl

case19 : Cover 19
case19 = reject3R 19 refl

case20 : Cover 20
case20 = reject2L 20 refl

case21 : Cover 21
case21 = reject3L 21 refl

case22 : Cover 22
case22 = reject2L 22 refl

case23 : Cover 23
case23 = reject5R 23 refl

case24 : Cover 24
case24 = reject2L 24 refl

case25 : Cover 25
case25 = reject3R 25 refl

case26 : Cover 26
case26 = reject2L 26 refl

case27 : Cover 27
case27 = reject3L 27 refl

case28 : Cover 28
case28 = reject2L 28 refl

case29 : Cover 29
case29 = (λ _ → Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero , refl)

case30 : Cover 30
case30 = reject2L 30 refl

case31 : Cover 31
case31 = reject3R 31 refl

case32 : Cover 32
case32 = reject2L 32 refl

case33 : Cover 33
case33 = reject3L 33 refl

case34 : Cover 34
case34 = reject2L 34 refl

case35 : Cover 35
case35 = reject5L 35 refl

case36 : Cover 36
case36 = reject2L 36 refl

case37 : Cover 37
case37 = reject3R 37 refl

case38 : Cover 38
case38 = reject2L 38 refl

case39 : Cover 39
case39 = reject3L 39 refl

case40 : Cover 40
case40 = reject2L 40 refl

case41 : Cover 41
case41 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne , refl)

case42 : Cover 42
case42 = reject2L 42 refl

case43 : Cover 43
case43 = reject3R 43 refl

case44 : Cover 44
case44 = reject2L 44 refl

case45 : Cover 45
case45 = reject3L 45 refl

case46 : Cover 46
case46 = reject2L 46 refl

case47 : Cover 47
case47 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne , refl)

case48 : Cover 48
case48 = reject2L 48 refl

case49 : Cover 49
case49 = reject3R 49 refl

case50 : Cover 50
case50 = reject2L 50 refl

case51 : Cover 51
case51 = reject3L 51 refl

case52 : Cover 52
case52 = reject2L 52 refl

case53 : Cover 53
case53 = reject5R 53 refl

case54 : Cover 54
case54 = reject2L 54 refl

case55 : Cover 55
case55 = reject3R 55 refl

case56 : Cover 56
case56 = reject2L 56 refl

case57 : Cover 57
case57 = reject3L 57 refl

case58 : Cover 58
case58 = reject2L 58 refl

case59 : Cover 59
case59 = (λ _ → Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne , refl)

case60 : Cover 60
case60 = reject2L 60 refl

case61 : Cover 61
case61 = reject3R 61 refl

case62 : Cover 62
case62 = reject2L 62 refl

case63 : Cover 63
case63 = reject3L 63 refl

case64 : Cover 64
case64 = reject2L 64 refl

case65 : Cover 65
case65 = reject5L 65 refl

case66 : Cover 66
case66 = reject2L 66 refl

case67 : Cover 67
case67 = reject3R 67 refl

case68 : Cover 68
case68 = reject2L 68 refl

case69 : Cover 69
case69 = reject3L 69 refl

case70 : Cover 70
case70 = reject2L 70 refl

case71 : Cover 71
case71 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne , refl)

case72 : Cover 72
case72 = reject2L 72 refl

case73 : Cover 73
case73 = reject3R 73 refl

case74 : Cover 74
case74 = reject2L 74 refl

case75 : Cover 75
case75 = reject3L 75 refl

case76 : Cover 76
case76 = reject2L 76 refl

case77 : Cover 77
case77 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero , refl)

case78 : Cover 78
case78 = reject2L 78 refl

case79 : Cover 79
case79 = reject3R 79 refl

case80 : Cover 80
case80 = reject2L 80 refl

case81 : Cover 81
case81 = reject3L 81 refl

case82 : Cover 82
case82 = reject2L 82 refl

case83 : Cover 83
case83 = reject5R 83 refl

case84 : Cover 84
case84 = reject2L 84 refl

case85 : Cover 85
case85 = reject3R 85 refl

case86 : Cover 86
case86 = reject2L 86 refl

case87 : Cover 87
case87 = reject3L 87 refl

case88 : Cover 88
case88 = reject2L 88 refl

case89 : Cover 89
case89 = (λ _ → Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne , refl)

case90 : Cover 90
case90 = reject2L 90 refl

case91 : Cover 91
case91 = reject3R 91 refl

case92 : Cover 92
case92 = reject2L 92 refl

case93 : Cover 93
case93 = reject3L 93 refl

case94 : Cover 94
case94 = reject2L 94 refl

case95 : Cover 95
case95 = reject5L 95 refl

case96 : Cover 96
case96 = reject2L 96 refl

case97 : Cover 97
case97 = reject3R 97 refl

case98 : Cover 98
case98 = reject2L 98 refl

case99 : Cover 99
case99 = reject3L 99 refl

case100 : Cover 100
case100 = reject2L 100 refl

case101 : Cover 101
case101 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne , refl)

case102 : Cover 102
case102 = reject2L 102 refl

case103 : Cover 103
case103 = reject3R 103 refl

case104 : Cover 104
case104 = reject2L 104 refl

case105 : Cover 105
case105 = reject3L 105 refl

case106 : Cover 106
case106 = reject2L 106 refl

case107 : Cover 107
case107 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero , refl)

case108 : Cover 108
case108 = reject2L 108 refl

case109 : Cover 109
case109 = reject3R 109 refl

case110 : Cover 110
case110 = reject2L 110 refl

case111 : Cover 111
case111 = reject3L 111 refl

case112 : Cover 112
case112 = reject2L 112 refl

case113 : Cover 113
case113 = reject5R 113 refl

case114 : Cover 114
case114 = reject2L 114 refl

case115 : Cover 115
case115 = reject3R 115 refl

case116 : Cover 116
case116 = reject2L 116 refl

case117 : Cover 117
case117 = reject3L 117 refl

case118 : Cover 118
case118 = reject2L 118 refl

case119 : Cover 119
case119 = (λ _ → Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne , refl)

case120 : Cover 120
case120 = reject2L 120 refl

case121 : Cover 121
case121 = reject3R 121 refl

case122 : Cover 122
case122 = reject2L 122 refl

case123 : Cover 123
case123 = reject3L 123 refl

case124 : Cover 124
case124 = reject2L 124 refl

case125 : Cover 125
case125 = reject5L 125 refl

case126 : Cover 126
case126 = reject2L 126 refl

case127 : Cover 127
case127 = reject3R 127 refl

case128 : Cover 128
case128 = reject2L 128 refl

case129 : Cover 129
case129 = reject3L 129 refl

case130 : Cover 130
case130 = reject2L 130 refl

case131 : Cover 131
case131 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero , refl)

case132 : Cover 132
case132 = reject2L 132 refl

case133 : Cover 133
case133 = reject3R 133 refl

case134 : Cover 134
case134 = reject2L 134 refl

case135 : Cover 135
case135 = reject3L 135 refl

case136 : Cover 136
case136 = reject2L 136 refl

case137 : Cover 137
case137 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero , refl)

case138 : Cover 138
case138 = reject2L 138 refl

case139 : Cover 139
case139 = reject3R 139 refl

case140 : Cover 140
case140 = reject2L 140 refl

case141 : Cover 141
case141 = reject3L 141 refl

case142 : Cover 142
case142 = reject2L 142 refl

case143 : Cover 143
case143 = reject5R 143 refl

case144 : Cover 144
case144 = reject2L 144 refl

case145 : Cover 145
case145 = reject3R 145 refl

case146 : Cover 146
case146 = reject2L 146 refl

case147 : Cover 147
case147 = reject3L 147 refl

case148 : Cover 148
case148 = reject2L 148 refl

case149 : Cover 149
case149 = (λ _ → Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne , refl)

case150 : Cover 150
case150 = reject2L 150 refl

case151 : Cover 151
case151 = reject3R 151 refl

case152 : Cover 152
case152 = reject2L 152 refl

case153 : Cover 153
case153 = reject3L 153 refl

case154 : Cover 154
case154 = reject2L 154 refl

case155 : Cover 155
case155 = reject5L 155 refl

case156 : Cover 156
case156 = reject2L 156 refl

case157 : Cover 157
case157 = reject3R 157 refl

case158 : Cover 158
case158 = reject2L 158 refl

case159 : Cover 159
case159 = reject3L 159 refl

case160 : Cover 160
case160 = reject2L 160 refl

case161 : Cover 161
case161 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero , refl)

case162 : Cover 162
case162 = reject2L 162 refl

case163 : Cover 163
case163 = reject3R 163 refl

case164 : Cover 164
case164 = reject2L 164 refl

case165 : Cover 165
case165 = reject3L 165 refl

case166 : Cover 166
case166 = reject2L 166 refl

case167 : Cover 167
case167 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne , refl)

case168 : Cover 168
case168 = reject2L 168 refl

case169 : Cover 169
case169 = reject3R 169 refl

case170 : Cover 170
case170 = reject2L 170 refl

case171 : Cover 171
case171 = reject3L 171 refl

case172 : Cover 172
case172 = reject2L 172 refl

case173 : Cover 173
case173 = reject5R 173 refl

case174 : Cover 174
case174 = reject2L 174 refl

case175 : Cover 175
case175 = reject3R 175 refl

case176 : Cover 176
case176 = reject2L 176 refl

case177 : Cover 177
case177 = reject3L 177 refl

case178 : Cover 178
case178 = reject2L 178 refl

case179 : Cover 179
case179 = (λ _ → Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne , refl)

case180 : Cover 180
case180 = reject2L 180 refl

case181 : Cover 181
case181 = reject3R 181 refl

case182 : Cover 182
case182 = reject2L 182 refl

case183 : Cover 183
case183 = reject3L 183 refl

case184 : Cover 184
case184 = reject2L 184 refl

case185 : Cover 185
case185 = reject5L 185 refl

case186 : Cover 186
case186 = reject2L 186 refl

case187 : Cover 187
case187 = reject3R 187 refl

case188 : Cover 188
case188 = reject2L 188 refl

case189 : Cover 189
case189 = reject3L 189 refl

case190 : Cover 190
case190 = reject2L 190 refl

case191 : Cover 191
case191 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero , refl)

case192 : Cover 192
case192 = reject2L 192 refl

case193 : Cover 193
case193 = reject3R 193 refl

case194 : Cover 194
case194 = reject2L 194 refl

case195 : Cover 195
case195 = reject3L 195 refl

case196 : Cover 196
case196 = reject2L 196 refl

case197 : Cover 197
case197 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne , refl)

case198 : Cover 198
case198 = reject2L 198 refl

case199 : Cover 199
case199 = reject3R 199 refl

case200 : Cover 200
case200 = reject2L 200 refl

case201 : Cover 201
case201 = reject3L 201 refl

case202 : Cover 202
case202 = reject2L 202 refl

case203 : Cover 203
case203 = reject5R 203 refl

case204 : Cover 204
case204 = reject2L 204 refl

case205 : Cover 205
case205 = reject3R 205 refl

case206 : Cover 206
case206 = reject2L 206 refl

case207 : Cover 207
case207 = reject3L 207 refl

case208 : Cover 208
case208 = reject2L 208 refl

case209 : Cover 209
case209 = (λ _ → Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne , refl)

case210 : Cover 210
case210 = reject2L 210 refl

case211 : Cover 211
case211 = reject3R 211 refl

case212 : Cover 212
case212 = reject2L 212 refl

case213 : Cover 213
case213 = reject3L 213 refl

case214 : Cover 214
case214 = reject2L 214 refl

case215 : Cover 215
case215 = reject5L 215 refl

case216 : Cover 216
case216 = reject2L 216 refl

case217 : Cover 217
case217 = reject3R 217 refl

case218 : Cover 218
case218 = reject2L 218 refl

case219 : Cover 219
case219 = reject3L 219 refl

case220 : Cover 220
case220 = reject2L 220 refl

case221 : Cover 221
case221 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne , refl)

case222 : Cover 222
case222 = reject2L 222 refl

case223 : Cover 223
case223 = reject3R 223 refl

case224 : Cover 224
case224 = reject2L 224 refl

case225 : Cover 225
case225 = reject3L 225 refl

case226 : Cover 226
case226 = reject2L 226 refl

case227 : Cover 227
case227 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne , refl)

case228 : Cover 228
case228 = reject2L 228 refl

case229 : Cover 229
case229 = reject3R 229 refl

case230 : Cover 230
case230 = reject2L 230 refl

case231 : Cover 231
case231 = reject3L 231 refl

case232 : Cover 232
case232 = reject2L 232 refl

case233 : Cover 233
case233 = reject5R 233 refl

case234 : Cover 234
case234 = reject2L 234 refl

case235 : Cover 235
case235 = reject3R 235 refl

case236 : Cover 236
case236 = reject2L 236 refl

case237 : Cover 237
case237 = reject3L 237 refl

case238 : Cover 238
case238 = reject2L 238 refl

case239 : Cover 239
case239 = (λ _ → Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero , refl)

case240 : Cover 240
case240 = reject2L 240 refl

case241 : Cover 241
case241 = reject3R 241 refl

case242 : Cover 242
case242 = reject2L 242 refl

case243 : Cover 243
case243 = reject3L 243 refl

case244 : Cover 244
case244 = reject2L 244 refl

case245 : Cover 245
case245 = reject5L 245 refl

case246 : Cover 246
case246 = reject2L 246 refl

case247 : Cover 247
case247 = reject3R 247 refl

case248 : Cover 248
case248 = reject2L 248 refl

case249 : Cover 249
case249 = reject3L 249 refl

case250 : Cover 250
case250 = reject2L 250 refl

case251 : Cover 251
case251 = (λ _ → Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne , refl)

case252 : Cover 252
case252 = reject2L 252 refl

case253 : Cover 253
case253 = reject3R 253 refl

case254 : Cover 254
case254 = reject2L 254 refl

case255 : Cover 255
case255 = reject3L 255 refl

case256 : Cover 256
case256 = reject2L 256 refl

case257 : Cover 257
case257 = (λ _ → Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne , refl)

case258 : Cover 258
case258 = reject2L 258 refl

case259 : Cover 259
case259 = reject3R 259 refl

case260 : Cover 260
case260 = reject2L 260 refl

case261 : Cover 261
case261 = reject3L 261 refl

case262 : Cover 262
case262 = reject2L 262 refl

case263 : Cover 263
case263 = reject5R 263 refl

case264 : Cover 264
case264 = reject2L 264 refl

case265 : Cover 265
case265 = reject3R 265 refl

case266 : Cover 266
case266 = reject2L 266 refl

case267 : Cover 267
case267 = reject3L 267 refl

case268 : Cover 268
case268 = reject2L 268 refl

case269 : Cover 269
case269 = (λ _ → Geometry.ternary27Point T.sspZero T.sspZero T.sspZero , refl)

allCases : AllFrom 0 270 Cover
allCases =
  (case0 ,
  (case1 ,
  (case2 ,
  (case3 ,
  (case4 ,
  (case5 ,
  (case6 ,
  (case7 ,
  (case8 ,
  (case9 ,
  (case10 ,
  (case11 ,
  (case12 ,
  (case13 ,
  (case14 ,
  (case15 ,
  (case16 ,
  (case17 ,
  (case18 ,
  (case19 ,
  (case20 ,
  (case21 ,
  (case22 ,
  (case23 ,
  (case24 ,
  (case25 ,
  (case26 ,
  (case27 ,
  (case28 ,
  (case29 ,
  (case30 ,
  (case31 ,
  (case32 ,
  (case33 ,
  (case34 ,
  (case35 ,
  (case36 ,
  (case37 ,
  (case38 ,
  (case39 ,
  (case40 ,
  (case41 ,
  (case42 ,
  (case43 ,
  (case44 ,
  (case45 ,
  (case46 ,
  (case47 ,
  (case48 ,
  (case49 ,
  (case50 ,
  (case51 ,
  (case52 ,
  (case53 ,
  (case54 ,
  (case55 ,
  (case56 ,
  (case57 ,
  (case58 ,
  (case59 ,
  (case60 ,
  (case61 ,
  (case62 ,
  (case63 ,
  (case64 ,
  (case65 ,
  (case66 ,
  (case67 ,
  (case68 ,
  (case69 ,
  (case70 ,
  (case71 ,
  (case72 ,
  (case73 ,
  (case74 ,
  (case75 ,
  (case76 ,
  (case77 ,
  (case78 ,
  (case79 ,
  (case80 ,
  (case81 ,
  (case82 ,
  (case83 ,
  (case84 ,
  (case85 ,
  (case86 ,
  (case87 ,
  (case88 ,
  (case89 ,
  (case90 ,
  (case91 ,
  (case92 ,
  (case93 ,
  (case94 ,
  (case95 ,
  (case96 ,
  (case97 ,
  (case98 ,
  (case99 ,
  (case100 ,
  (case101 ,
  (case102 ,
  (case103 ,
  (case104 ,
  (case105 ,
  (case106 ,
  (case107 ,
  (case108 ,
  (case109 ,
  (case110 ,
  (case111 ,
  (case112 ,
  (case113 ,
  (case114 ,
  (case115 ,
  (case116 ,
  (case117 ,
  (case118 ,
  (case119 ,
  (case120 ,
  (case121 ,
  (case122 ,
  (case123 ,
  (case124 ,
  (case125 ,
  (case126 ,
  (case127 ,
  (case128 ,
  (case129 ,
  (case130 ,
  (case131 ,
  (case132 ,
  (case133 ,
  (case134 ,
  (case135 ,
  (case136 ,
  (case137 ,
  (case138 ,
  (case139 ,
  (case140 ,
  (case141 ,
  (case142 ,
  (case143 ,
  (case144 ,
  (case145 ,
  (case146 ,
  (case147 ,
  (case148 ,
  (case149 ,
  (case150 ,
  (case151 ,
  (case152 ,
  (case153 ,
  (case154 ,
  (case155 ,
  (case156 ,
  (case157 ,
  (case158 ,
  (case159 ,
  (case160 ,
  (case161 ,
  (case162 ,
  (case163 ,
  (case164 ,
  (case165 ,
  (case166 ,
  (case167 ,
  (case168 ,
  (case169 ,
  (case170 ,
  (case171 ,
  (case172 ,
  (case173 ,
  (case174 ,
  (case175 ,
  (case176 ,
  (case177 ,
  (case178 ,
  (case179 ,
  (case180 ,
  (case181 ,
  (case182 ,
  (case183 ,
  (case184 ,
  (case185 ,
  (case186 ,
  (case187 ,
  (case188 ,
  (case189 ,
  (case190 ,
  (case191 ,
  (case192 ,
  (case193 ,
  (case194 ,
  (case195 ,
  (case196 ,
  (case197 ,
  (case198 ,
  (case199 ,
  (case200 ,
  (case201 ,
  (case202 ,
  (case203 ,
  (case204 ,
  (case205 ,
  (case206 ,
  (case207 ,
  (case208 ,
  (case209 ,
  (case210 ,
  (case211 ,
  (case212 ,
  (case213 ,
  (case214 ,
  (case215 ,
  (case216 ,
  (case217 ,
  (case218 ,
  (case219 ,
  (case220 ,
  (case221 ,
  (case222 ,
  (case223 ,
  (case224 ,
  (case225 ,
  (case226 ,
  (case227 ,
  (case228 ,
  (case229 ,
  (case230 ,
  (case231 ,
  (case232 ,
  (case233 ,
  (case234 ,
  (case235 ,
  (case236 ,
  (case237 ,
  (case238 ,
  (case239 ,
  (case240 ,
  (case241 ,
  (case242 ,
  (case243 ,
  (case244 ,
  (case245 ,
  (case246 ,
  (case247 ,
  (case248 ,
  (case249 ,
  (case250 ,
  (case251 ,
  (case252 ,
  (case253 ,
  (case254 ,
  (case255 ,
  (case256 ,
  (case257 ,
  (case258 ,
  (case259 ,
  (case260 ,
  (case261 ,
  (case262 ,
  (case263 ,
  (case264 ,
  (case265 ,
  (case266 ,
  (case267 ,
  (case268 ,
  (case269 ,
  tt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- Every admissible representative has an explicit inverse witness.
wheel270CompleteFin :
  (i : Fin 270) → Wheel270Survives (Fin.toℕ i) →
  Σ Geometry.Ternary27Point
    (λ p → Codec.cubeToWheel270 p ≡ Fin.toℕ i)
wheel270CompleteFin i =
  subst Cover (shiftZero i) (allAt 0 allCases i)

-- Consume the REAL certified arithmetic axes. No parallel oracle.
certifiedWheel270ToGuards :
  (a2 a3 a5 : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus a2 ≡ 2 →
  Pair.primeModulus a3 ≡ 3 →
  Pair.primeModulus a5 ≡ 5 →
  (n : Nat) →
  Pair.AllPairSurvive (a2 ∷ a3 ∷ a5 ∷ []) n →
  Wheel270Survives n
certifiedWheel270ToGuards a2 a3 a5 eq2 eq3 eq5 n
  (h2 , (h3 , (h5 , tt))) =
  ( subst
      (λ p → ((n % p ≢ 0) × ((n + 2) % p ≢ 0)))
      eq2 h2
  , ( subst
        (λ p → ((n % p ≢ 0) × ((n + 2) % p ≢ 0)))
        eq3 h3
    , ( subst
          (λ p → ((n % p ≢ 0) × ((n + 2) % p ≢ 0)))
          eq5 h5
      , tt )))

wheel270CompleteCertified :
  (a2 a3 a5 : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus a2 ≡ 2 →
  Pair.primeModulus a3 ≡ 3 →
  Pair.primeModulus a5 ≡ 5 →
  (i : Fin 270) →
  Pair.AllPairSurvive (a2 ∷ a3 ∷ a5 ∷ [])
    (Fin.toℕ i) →
  Σ Geometry.Ternary27Point
    (λ p → Codec.cubeToWheel270 p ≡ Fin.toℕ i)
wheel270CompleteCertified a2 a3 a5 eq2 eq3 eq5 i h =
  wheel270CompleteFin i
    (certifiedWheel270ToGuards a2 a3 a5
      eq2 eq3 eq5 (Fin.toℕ i) h)

-- Stronger observed decoder guarantee on every admissible residue:
-- no silent nothing case, and the recovered point is typed.
wheel270SurvivorDecodes :
  (i : Fin 270) → Wheel270Survives (Fin.toℕ i) →
  Σ Geometry.Ternary27Point
    (λ p → Codec.wheel270ToCube (Fin.toℕ i) ≡ just p)
wheel270SurvivorDecodes i survives
  with wheel270CompleteFin i survives
... | p , equalCode =
  p , trans
    (sym (cong Codec.wheel270ToCube equalCode))
    (Codec.wheel270DecodeEncode p)

-- Genuine modular projections. The y/z plane is modulo 3^3,
-- whereas x is modulo 5. Parity is fixed by the original codec.
wheel270ProjectionMod27 :
  (x y z : T.SSPTrit) →
  Codec.cubeToWheel270 (Geometry.ternary27Point x y z) % 27
    ≡ (14 + 3 * Codec.ternaryDigit y
          + 9 * Codec.ternaryDigit z) % 27
wheel270ProjectionMod27 T.sspNegOne T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspNegOne T.sspNegOne T.sspZero = refl
wheel270ProjectionMod27 T.sspNegOne T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod27 T.sspNegOne T.sspZero T.sspNegOne = refl
wheel270ProjectionMod27 T.sspNegOne T.sspZero T.sspZero = refl
wheel270ProjectionMod27 T.sspNegOne T.sspZero T.sspPosOne = refl
wheel270ProjectionMod27 T.sspNegOne T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspNegOne T.sspPosOne T.sspZero = refl
wheel270ProjectionMod27 T.sspNegOne T.sspPosOne T.sspPosOne = refl
wheel270ProjectionMod27 T.sspZero T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspZero T.sspNegOne T.sspZero = refl
wheel270ProjectionMod27 T.sspZero T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod27 T.sspZero T.sspZero T.sspNegOne = refl
wheel270ProjectionMod27 T.sspZero T.sspZero T.sspZero = refl
wheel270ProjectionMod27 T.sspZero T.sspZero T.sspPosOne = refl
wheel270ProjectionMod27 T.sspZero T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspZero T.sspPosOne T.sspZero = refl
wheel270ProjectionMod27 T.sspZero T.sspPosOne T.sspPosOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspNegOne T.sspZero = refl
wheel270ProjectionMod27 T.sspPosOne T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspZero T.sspNegOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspZero T.sspZero = refl
wheel270ProjectionMod27 T.sspPosOne T.sspZero T.sspPosOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod27 T.sspPosOne T.sspPosOne T.sspZero = refl
wheel270ProjectionMod27 T.sspPosOne T.sspPosOne T.sspPosOne = refl

wheel270ProjectionMod5 :
  (x y z : T.SSPTrit) →
  Codec.cubeToWheel270 (Geometry.ternary27Point x y z) % 5
    ≡ (1 + 3 * Codec.ternaryDigit x) % 5
wheel270ProjectionMod5 T.sspNegOne T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspNegOne T.sspNegOne T.sspZero = refl
wheel270ProjectionMod5 T.sspNegOne T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod5 T.sspNegOne T.sspZero T.sspNegOne = refl
wheel270ProjectionMod5 T.sspNegOne T.sspZero T.sspZero = refl
wheel270ProjectionMod5 T.sspNegOne T.sspZero T.sspPosOne = refl
wheel270ProjectionMod5 T.sspNegOne T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspNegOne T.sspPosOne T.sspZero = refl
wheel270ProjectionMod5 T.sspNegOne T.sspPosOne T.sspPosOne = refl
wheel270ProjectionMod5 T.sspZero T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspZero T.sspNegOne T.sspZero = refl
wheel270ProjectionMod5 T.sspZero T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod5 T.sspZero T.sspZero T.sspNegOne = refl
wheel270ProjectionMod5 T.sspZero T.sspZero T.sspZero = refl
wheel270ProjectionMod5 T.sspZero T.sspZero T.sspPosOne = refl
wheel270ProjectionMod5 T.sspZero T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspZero T.sspPosOne T.sspZero = refl
wheel270ProjectionMod5 T.sspZero T.sspPosOne T.sspPosOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspNegOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspNegOne T.sspZero = refl
wheel270ProjectionMod5 T.sspPosOne T.sspNegOne T.sspPosOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspZero T.sspNegOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspZero T.sspZero = refl
wheel270ProjectionMod5 T.sspPosOne T.sspZero T.sspPosOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspPosOne T.sspNegOne = refl
wheel270ProjectionMod5 T.sspPosOne T.sspPosOne T.sspZero = refl
wheel270ProjectionMod5 T.sspPosOne T.sspPosOne T.sspPosOne = refl

wheel270ProjectionMod2 :
  (p : Geometry.Ternary27Point) →
  Codec.cubeToWheel270 p % 2 ≡ 1
wheel270ProjectionMod2 = Codec.wheel270ModTwo

survivorFibreFactorisation : 1 * 9 * 3 ≡ 27
survivorFibreFactorisation = refl

-- Forward direction is already source-owned by Codec:
-- Codec.wheel270PassesCertifiedTwoThreeFive.
-- Together with wheel270CompleteCertified this is the finite
-- typed-cube / prime-2,3,5 wheel-survivor equivalence.
-- No extension from local survival to actual twin primality.

------------------------------------------------------------------------
-- A concrete DOUBLE-COMPOSITE residue inside the FULL 27-point cube.
-- r = 119 survives p=2,3,5, but 119=7*17 and 121=11*11.
-- Reuse the original genuine Composite witness constructor owner.
------------------------------------------------------------------------

wheel270CubePoint119 :
  Codec.cubeToWheel270
    (Geometry.ternary27Point
      T.sspZero T.sspPosOne T.sspPosOne) ≡ 119
wheel270CubePoint119 = refl

wheel270119Survives : Wheel270Survives 119
wheel270119Survives =
  ((λ ()) , (λ ())) ,
  (((λ ()) , (λ ())) ,
    (((λ ()) , (λ ())) , tt))

wheel270119IsComposite : NatPrime.Composite 119
wheel270119IsComposite =
  Composite.twoNontrivialFactorsAreComposite 119
    (Composite.twoNontrivialFactors 5 15 refl)

wheel270121IsComposite : NatPrime.Composite 121
wheel270121IsComposite =
  Composite.twoNontrivialFactorsAreComposite 121
    (Composite.twoNontrivialFactors 9 9 refl)

wheel270119SurvivalCannotProveTwin :
  Twin.TwinPrimeAt 119 → ⊥
wheel270119SurvivalCannotProveTwin genuine =
  NatPrime.composite⇒¬prime wheel270119IsComposite
    (proj₁ genuine)

wheel270121NotPrime : NatPrime.Prime 121 → ⊥
wheel270121NotPrime =
  NatPrime.composite⇒¬prime wheel270121IsComposite

-- All three are exact separate mathematical facts:
-- wheel270CubePoint119, wheel270119Survives,
-- wheel270119IsComposite and wheel270121IsComposite.
-- A type-preserving bijection between finite sieve survivors and
-- cube points cannot manufacture the missing prime certificates.
