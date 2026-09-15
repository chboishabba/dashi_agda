module DASHI.Physics.Closure.NSTriadKNR571LeanGateAEnvelopeReceiptRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNR571LeanGateAEnvelopeReceiptExact as Receipt

leanA1ReceiptObserved : Receipt.leanGateAA1ReceiptObserved Receipt.currentR571LeanGateAReceipt ≡ true
leanA1ReceiptObserved = refl

leanA2ReceiptObserved : Receipt.leanGateAA2ReceiptObserved Receipt.currentR571LeanGateAReceipt ≡ true
leanA2ReceiptObserved = refl

agdaA1SampleTransportStillOpen : Receipt.agdaGateAA1SampleTransportObserved Receipt.currentR571LeanGateAReceipt ≡ false
agdaA1SampleTransportStillOpen = refl

agdaA2SampleTransportStillOpen : Receipt.agdaGateAA2SampleTransportObserved Receipt.currentR571LeanGateAReceipt ≡ false
agdaA2SampleTransportStillOpen = refl

g2StillOpen : Receipt.g2PhysicalStateEnvelopePaid Receipt.currentR571LeanGateAReceipt ≡ false
g2StillOpen = refl

g1StillOpen : Receipt.g1PhysicalStateEnvelopePaid Receipt.currentR571LeanGateAReceipt ≡ false
g1StillOpen = refl

r568StillOpen : Receipt.r568Paid Receipt.currentR571LeanGateAReceipt ≡ false
r568StillOpen = refl
