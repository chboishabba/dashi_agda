{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanContinuumProducerValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact as Producer
import DASHI.Physics.Foundations.CommonActionQFTGRContinuumProducerCompilerExact as Compiler

balabanContinuumProducerCompiler : Producer.ProofLevel
balabanContinuumProducerCompiler = Producer.balabanContinuumProducerCompilerLevel

commonMetricContinuumProducerCompiler : Compiler.ProofLevel
commonMetricContinuumProducerCompiler =
  Compiler.commonActionQFTGRContinuumProducerCompilerLevel
