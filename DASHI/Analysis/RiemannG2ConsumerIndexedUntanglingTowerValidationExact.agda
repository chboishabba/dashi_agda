module DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerValidationExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH

geometry : RH.RHCellUntanglingGeometry
geometry = RH.rhCellUntanglingGeometry

collision : RH.RHCellFineSensitiveConsumer
collision = RH.rhCellFineSensitiveConsumer

boundary : RH.RHConsumerIndexedUntanglingBoundary
boundary = RH.canonicalRHConsumerIndexedUntanglingBoundary
