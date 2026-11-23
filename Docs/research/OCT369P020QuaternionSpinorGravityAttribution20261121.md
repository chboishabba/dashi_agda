# OCT369 P0.20 — quaternion / spinor / gravity original-source attribution and acceptance

Date: 2026-11-21. Programme priority: OCTUPOLE -> ANTIGRAVITY P0.
This module is an **original-source consumer**, not a new fundamental quaternion or Spin theory.

## Reuse and proof owners
- Hamilton quaternion multiplication; Clifford/Cartan Spin(3)=SU(2) cover; standard SU2/Pauli two-component spinor; pure-gauge flat-connection and noncommuting curvature calculations are mathematical/physics prior art.
- Exact DASHI finite double cover: \`DASHI/Algebra/FiniteQuaternionDoubleCover.agda\`, specifically Q8->V4, two signs, distinct from full continuous Spin3.
- Exact rational rotor: \`DASHI/Mathematics/Topology/AlexanderHornedQuaternionC3SpinExact.agda\`, q=(1+i+j+k)/2, q^3=-1 and x,y,z -> z,x,y.
- Exact discrete-lift correction: \`DASHI/Mathematics/Topology/AlexanderHornedC3SpinLiftSplitExact.agda\`; continuous path-selected rotor q cubed -1; strict C3 section -q cubed 1; rephased factor cocycle. As prior documentation explicitly warns: never say every C3 spinor lift has order six.
- Group-law interoperability: \`DASHI/Physics/QuantumVacuum/CasimirQuaternionSU2GroupLawBridgeExact.agda\`; concrete group law identification is NOT automatic physical structural-group identification.
- \`DASHI/Algebra/CliffordSpinLift.agda\` and \`DASHI/Physics/CliffordEvenLiftBridge.agda\` host records and selected bridges only, not a complete spacetime spinor matter action.
- \`DASHI/Physics/QFT/SpinorRepresentationReceipt.agda\` has an explicit characteristic-two warning: no fermionic minus sign at char 2.
- GR first-order owner \`DASHI/Physics/Closure/GRFirstOrderGravityScope.agda\` declares missing structure group/vierbein/Lorentz spin connection/curvature/Palatini action/sourced Einstein and Bianchi obligations; \`DASHI/Unified/TOEGaugeQFTGRRealizationExact.agda\` retains selected real action/stress/calibration obligations as false.
- Kang et al., Nature 2026, DOI 10.1038/s41586-026-11172-5 own PtMn3/MgO/PtMn3 octupole switching, magnetic order and 363% TMR. This project cannot claim experimental gravity coupling or infer it from the article.

## New finite regression
\`scripts/check_oct369_p020_quaternion_spinor_gravity.py\`: **57 exact SymPy assertions PASS locally**, all nine path-cocycle entries and nine coboundary checks, strict discrete C3 lift, spinor SU2 matrix, quaternion conjugation, zero-net-moment Mn 3c trial texture, central sign invariance of magnetic bilinears, and two distinct gauge-curvature controls. Its receipt declares \`physical_vierbein_spin_connection_supplied=false\`, \`physical_stress_energy_or_metric_field_derived=false\`, \`real_PtMn3_parameter_fit_or_gravity_anomaly=false\`.

## Same-object P0 next payment
A curved-space Dirac spinor must use a spacetime tetrad and Lorentz Spin(3,1) connection, with a source-selected material+EM+octupole action. SU2 crystal-spin rotations may embed in this representation under a specified local rest frame but neither equal the YM SU2 group nor supply physical Riemann curvature by group isomorphism alone. Recover actual magnetized film states, current-induced torque and material stresses, then derive vielbein/metric variation, conserved T_munu, field equations and independent gravity or human lift measurements. Superconducting/pulsed RF/Schumann remain separate source-controlled hypotheses. P0 remains OPEN.
