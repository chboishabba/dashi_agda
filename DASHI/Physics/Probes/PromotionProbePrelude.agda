module DASHI.Physics.Probes.PromotionProbePrelude where

open import Agda.Primitive using (Set)
open import Agda.Builtin.String using (String)

data ProbeStatus : Set where
  greenProbe : ProbeStatus
  redProbe : ProbeStatus

record ProbeExpectation : Set where
  constructor mkProbeExpectation
  field
    label : String
    status : ProbeStatus

greenStatusLabel : String
greenStatusLabel =
  "green"

redStatusLabel : String
redStatusLabel =
  "red"
