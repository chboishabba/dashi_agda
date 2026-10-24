module DASHI.Foundations.C3NineSiteBalancedChartExact where

-- Exact nine-site <-> two-balanced-trit chart. No topology is inferred
-- from the finite chart without an explicit continuous lift.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import DASHI.Foundations.C3NineSiteAlternatingOrbitExact using
  (Site; TL; TM; TR; ML; MM; MR; BL; BM; BR; Triple;
   triple; configuration; T12)
open import DASHI.Algebra.BalancedTernary using
  (Trit; neg; zero; pos)

record ChartPoint : Set where
  constructor point
  field
    row : Trit
    column : Trit
open ChartPoint public

encode : Site → ChartPoint
encode TL = point neg neg
encode TM = point neg zero
encode TR = point neg pos
encode ML = point zero neg
encode MM = point zero zero
encode MR = point zero pos
encode BL = point pos neg
encode BM = point pos zero
encode BR = point pos pos

decode : ChartPoint → Site
decode (point neg neg) = TL
decode (point neg zero) = TM
decode (point neg pos) = TR
decode (point zero neg) = ML
decode (point zero zero) = MM
decode (point zero pos) = MR
decode (point pos neg) = BL
decode (point pos zero) = BM
decode (point pos pos) = BR

decodeEncode : ∀ site → decode (encode site) ≡ site
decodeEncode TL = refl
decodeEncode TM = refl
decodeEncode TR = refl
decodeEncode ML = refl
decodeEncode MM = refl
decodeEncode MR = refl
decodeEncode BL = refl
decodeEncode BM = refl
decodeEncode BR = refl

encodeDecode : ∀ chart → encode (decode chart) ≡ chart
encodeDecode (point neg neg) = refl
encodeDecode (point neg zero) = refl
encodeDecode (point neg pos) = refl
encodeDecode (point zero neg) = refl
encodeDecode (point zero zero) = refl
encodeDecode (point zero pos) = refl
encodeDecode (point pos neg) = refl
encodeDecode (point pos zero) = refl
encodeDecode (point pos pos) = refl

chartInjective : ∀ {a b} → encode a ≡ encode b → a ≡ b
chartInjective {a} {b} eq =
  trans (sym (decodeEncode a))
    (trans (cong decode eq) (decodeEncode b))

chartTriple : Triple Site → Triple ChartPoint
chartTriple (triple a b c) = triple (encode a) (encode b) (encode c)

chartConfiguration : T12 → Triple ChartPoint
chartConfiguration t = chartTriple (configuration t)
