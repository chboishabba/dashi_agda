{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2LinearityTest where

import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2LinearityExact as P1

linearityRegression = P1.round143LinearityIsPathDerivativeAlgebra
physicsRegression = P1.noPhysicalSourceLeafInFirstVariationLinearity
