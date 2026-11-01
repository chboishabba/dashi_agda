# NS Sprint 90 Epsilon Budget Solver

- Contract: `ns_sprint90_epsilon_budget_solver`
- Decision: `FAIL_CLOSED`
- Condition: `C*(K*)^-1/2*H1Tail <= epsilon*nu`
- C: `1`
- epsilon: `0.1`
- Candidate pairs evaluated: `12`
- Accepted candidate pairs: `0`

## Gate Results

- G1 AllowedCandidateSupplied: `PASS`
- G2 PointwiseH1TailSupplied: `PASS`
- G3 IndependentEpsilonCoefficientSupplied: `FAIL_CLOSED`
- G4 EvidenceComplete: `FAIL_CLOSED`
- G5 ScalarAbsorptionAccepted: `FAIL_CLOSED`

## Conclusion

The audit fails closed. Leray-only and time-integrated-only tails are not pointwise H1-tail estimates. The local-enstrophy candidate is pointwise but lacks an independent epsilon coefficient. The required independent-coefficient law is listed as the necessary law shape, but it is not supplied.

No Clay Navier-Stokes promotion or scalar absorption closure is certified by this calculator.
