module DASHI.Physics.YangMills.YangMillsSubmissionRound10Ledger where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Round10LedgerEntry : Set where
  field
    name statement : String
    level : ProofLevel

open Round10LedgerEntry public

factorialCoefficientDischarge : Round10LedgerEntry
factorialCoefficientDischarge = record
  { name = "Bishop reciprocal-factorial coefficient step"
  ; statement = "Natural denominator growth and rational reciprocal antitonicity construct both concrete sine/cosine coarse-ratio fields."
  ; level = machineChecked
  }

transformedSeriesConvergence : Round10LedgerEntry
transformedSeriesConvergence = record
  { name = "Bishop transformed-series convergence"
  ; statement = "Pointwise term equivalence and term parity transport convergence; transformed convergence is no longer an independent analytic input."
  ; level = machineChecked
  }

alternatingOrderClosure : Round10LedgerEntry
alternatingOrderClosure = record
  { name = "Bishop alternating order closure"
  ; statement = "Increasing lower and decreasing upper subsequences converging to the represented value construct the setoid alternating bracket record."
  ; level = machineChecked
  }

concreteSineCosineInterlacing : Round10LedgerEntry
concreteSineCosineInterlacing = record
  { name = "Concrete sine/cosine interlacing"
  ; statement = "The actual signed factorial partial sums must inhabit the monotone lower/upper subsequence data and adjacent omitted-term identities."
  ; level = conditional
  }

ordinaryFiniteGeometricBound : Round10LedgerEntry
ordinaryFiniteGeometricBound = record
  { name = "Finite geometric Step-V bound"
  ; statement = "For Bishop-real 0 <= q < 1, every finite geometric partial sum is bounded by (1-q)^(-1)."
  ; level = machineChecked
  }

polynomialWeightedShellBound : Round10LedgerEntry
polynomialWeightedShellBound = record
  { name = "Polynomially weighted shell bound"
  ; statement = "The finite-prefix plus larger-ratio absorption theorem for n^p q^n remains to be inhabited on the concrete carrier."
  ; level = conditional
  }

p06LightweightInterface : Round10LedgerEntry
p06LightweightInterface = record
  { name = "Lightweight P06 physical leaf"
  ; statement = "Support, reduced-skeleton, decoration, decomposition and bounded-fibre propositions can be checked without importing the cyclotomic DFT regression graph."
  ; level = machineChecked
  }

p06PhysicalInhabitants : Round10LedgerEntry
p06PhysicalInhabitants = record
  { name = "P06 physical inhabitants"
  ; statement = "Literal support, linear reduced complexity, decoration multiplicity, canonical decoding and the legacy bridge remain physical inputs."
  ; level = conditional
  }

remainingPhysicalFrontier : Round10LedgerEntry
remainingPhysicalFrontier = record
  { name = "P11/P10/P33/Gate4/global frontier"
  ; statement = "Startup/tail entropy payment, large-field suppression, transverse ellipticity, CMP109 physical pairing, RG limits, OS reconstruction and positive SI gap remain conditional."
  ; level = conditional
  }
