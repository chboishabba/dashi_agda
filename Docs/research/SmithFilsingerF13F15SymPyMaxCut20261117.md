# F13 / F15 / D1 exact SymPy maximum cut — 17 November 2026

## What was actually completed
A new exact 3-layer (soil, air, ionosphere), 2-polarization-per-layer *reduced transverse* finite-volume Maxwell-wave resolvent, plus a signed full-cycle work audit and uncertainty certificate. **25/25 separately run SymPy exact rational/symbolic tests PASS.** This is not a full 3D dyadic Green solution, measured solar-source transfer or Agda-kernel proof.

### Source-first reuse
Existing canonical owners: BalabanFiniteCoerciveGreen (finite inverse/norm), BalabanSide4ScalarGreenConvolutionExact (real periodic elliptic inverse), SmithFilsingerCoerciveGreenRetardedWeldExact (delayed original source and launch clock), SmithFilsingerReplenishedCycleCapExact (repeatable work law), SmithFilsingerSpaceTimePoyntingTelescopeExact (signed source and outgoing flux), and KSW668FullVectorMaxwellJetExact (pointwise full-vector Poynting). No duplicate Green theorem was constructed.

### F13 exact reduced layered operator
New code: scripts/smith_filsinger_layered_green_sympy.py and scripts/test_smith_filsinger_layered_green_sympy.py.

C e'' + (P+H) e' + K e = J_env + J_ctrl, with
G(s,k2) = [s² C + s(P+H) + K(k2)]^(-1).
C, P and K are positive symmetric in the chosen rational model; H is antisymmetric Hall coupling. K couples soil–air–ionosphere in the vertical direction, and k2 >= 0 is the in-plane squared Fourier wave number. Layer parameters are **exact mathematical fixture numbers**, not measured physical constants.

Exact results checked: both-sided 6×6 inverse, nonzero soil response to a hypothetical ionosphere source, Hall reversal transpose symmetry, positive symmetric part, and four lateral k² modes 0,1/3,2,7/2. This is a limited *transverse Galerkin-wave* reduction. It does NOT implement full Maxwell longitudinal constraints, true 3D dyadic polarization with oblique geomagnetic orientation, physical source strength or calibrated original collector response.

Implicit midpoint consumes only current/past source steps and proves the exact finite work identity
delta U = W_env + W_ctrl - Q_Pedersen, with W_Hall = 0.
The global algebraic spatial inverse need not obey a physical finite propagation speed: exact time-step causality is NOT a Maxwell light-cone theorem.

External method authorities: https://mfem.org/maxwell-notes/ ; https://angeo.copernicus.org/articles/39/189/2021/ ; https://agupubs.onlinelibrary.wiley.com/doi/full/10.1029/2007JA012911 .

### F15 independently replenished work
New Agda source: DASHI/Physics/Motors/SmithFilsingerHundredfoldSourceFundingExact.agda. Imports canonical Cycle.workPaidAfterStorageReturns. A hypothetical fully restored >=100-fold useful load satisfies
W_natural + W_controller = 100 W_controller + W_excess + losses.
It cannot be paid by one-time storage depletion. A model cycle natural=100, controller=1, useful=100, loss=1, storage=5->5 proves mathematical *consistency only*.

SymPy restored_cycle_audit rejects missing independent natural/load measurements, unsourced load, non-restored storage, source-double-count and work violations. Its measurement flags in tests are assumed and MUST NOT be misread as real experimental data. uncertainty_gain_certificate requires certified independent intervals and 0 storage change. Robust >=100-fold requires load_lower >= 100*controller_upper. Thus load=100 and controller interval [1,1.1] gives a robust 100/1.1 = 90.909... fold bound and FAILS 100-fold robust claim, despite nominal ratio 100.

### D1 SymPy is not Agda
The new scripts/check_smith_filsinger_sympy_gate.py runs exact SymPy regressions, checks expected Agda source names and holes/postulates, and ALWAYS reports "agda_kernel": "NOT_RUN", "D1_kernel_gate": "OPEN". The actual pinned Agda compiler check remains scripts/check_smith_filsinger_formal_weld_agda29.sh, which now includes the new F15 funding module. No Agda/Nix executable was available here. A matching polynomial identity checked by SymPy is NOT an Agda typecheck. Full exact-head combined pytest was not run here; 25/25 is a separately run source-equivalent SymPy result.

### Remaining strict physical criteria
F13: full 3D retarded layered Maxwell dyadic, explicit Hall/Pedersen/parallel conductivity with geomagnetic orientation; correct open-boundary Green kernel and light-cone support; nonlinear localized plasma source/return, displacement-current correct measured terminal V,I; environmental source and backaction.

F15: independently measured and replenished **same-original** solar-attributed signed work, all controller/ion/thermal losses, closed source/receiver storage, synchronized source and output observations, and uncertainty enclosure. All unavailable in this session. Therefore F13 physical and F15 measured remain OPEN.

D1: actual pinned Agda 2.9 typecheck on exact branch head remains OPEN. SymPy exact tests are a useful independent oracle, NOT replacement.

Attribution: classical Maxwell/Green and Hall/Pedersen background reused; user-origin Smith/Filsinger nonlinear Sun–Earth source hypothesis remains conditional. No ESD edits or premature TOE promotion.
