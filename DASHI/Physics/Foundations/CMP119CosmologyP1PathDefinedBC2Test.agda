{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Test where

import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Exact as P1

firstVariationRegression = P1.bc2FirstVariationIsPathDerivativeByDefinition
sameDensityRegression = P1.pathDefinedBC2KeepsExactCarrierPotential
