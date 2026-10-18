module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Cut

b1PairExtractionReceipt : Cut.b1LiteralDFLPairExtractionClosed ≡ true
b1PairExtractionReceipt = refl

b2PairExtractionReceipt : Cut.b2LiteralDFLDHHPairExtractionClosed ≡ true
b2PairExtractionReceipt = refl

b3PairExtractionReceipt : Cut.b3LiteralDHHPairExtractionClosed ≡ true
b3PairExtractionReceipt = refl
