module DASHI.ComputerScience.ComputerScienceQuantumFibreValidationExact where

------------------------------------------------------------------------
-- SMALL QUANTUM / CROSS-PARADIGM VALIDATION ROOT
--
-- Kept separate from the classical CS validation root to avoid unnecessarily
-- enlarging ordinary Agda elaboration cones.
------------------------------------------------------------------------

import DASHI.ComputerScience.FibreProgramComplexityExact
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact
import DASHI.ComputerScience.ShorClassicalQuantumFibreComparisonExact
import DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact

import DASHI.Algebra.Quantum.FiniteQuantumRegister
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite
import DASHI.Algebra.Quantum.GeneralShor
import DASHI.Algebra.Quantum.FiniteQutrit
import DASHI.Algebra.Quantum.QutritWeyl
import DASHI.Algebra.Quantum.DASHIQuantumBridge
import DASHI.Algebra.Quantum.DASHIHybridExecution
import DASHI.Algebra.Quantum.DASHIShorProductiveJoin

import DASHI.Crypto.ShorOrderFinding
import DASHI.Crypto.ShorFactoring
import DASHI.Crypto.ShorProgram
