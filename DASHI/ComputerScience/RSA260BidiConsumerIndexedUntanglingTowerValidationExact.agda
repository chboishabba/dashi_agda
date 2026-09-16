module DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA

exactTower : RSA.RSAReplayUntanglingTower
exactTower = RSA.rsaReplayUntanglingTower

roundTrip :
  (packet : RSA.GeneratorReplayPacket) →
  RSA.decodeRSAReplayTower (RSA.encodeRSAReplayTower packet) ≡ packet
roundTrip = RSA.rsaReplayTowerRoundTrip

boundary : RSA.RSAConsumerIndexedUntanglingBoundary
boundary = RSA.canonicalRSAConsumerIndexedUntanglingBoundary
