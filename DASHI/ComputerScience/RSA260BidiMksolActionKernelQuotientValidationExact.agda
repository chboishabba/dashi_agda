module DASHI.ComputerScience.RSA260BidiMksolActionKernelQuotientValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiMksolActionKernelQuotientExact as Q

boundary : Q.MksolActionKernelQuotientBoundary
boundary = Q.canonicalMksolActionKernelQuotientBoundary

runtime : Q.MksolActionKernelRuntimeReceipt
runtime = Q.currentMksolActionKernelRuntimeReceipt

firstResidual : Q.MksolActionKernelResidual
firstResidual = Q.firstMksolActionKernelResidual
