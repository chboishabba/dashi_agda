module DASHI.ComputerScience.RSA260BidiMksolVContextStressValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiMksolVContextStressExact as Stress

boundary : Stress.MksolVContextStressBoundary
boundary = Stress.canonicalMksolVContextStressBoundary

runtime : Stress.MksolVContextStressRuntimeReceipt
runtime = Stress.currentMksolVContextStressRuntimeReceipt

firstResidual : Stress.MksolVContextStressResidual
firstResidual = Stress.firstMksolVContextStressResidual
