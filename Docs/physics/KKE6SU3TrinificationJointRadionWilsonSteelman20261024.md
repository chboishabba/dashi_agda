# KK × E6/SU3³: the full radion + electromagnetic Wilson-line steelman (2026-10-24)

Owner: [Agda KK PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241). Executable: `scripts/check_kk_e6_trinification_joint_radion_wilson.py`. This is the **later, stronger consumer** and supersedes the massless-vector-only/radion-only viability speculation in the prior 240/243 atlas.

## Original scientific and repository authority

- R. Slansky, *Group theory for unified model building*, *Physics Reports* 79 (1981) 1–128, DOI 10.1016/0370-1573(81)90092-2, source-root tables 53/58 for E8⊃E6×SU3, E6⊃SU3×SU3×SU3 and branching dimensions. These decompositions are EXTERNAL ESTABLISHED representation theory, NOT a DASHI discovery.
- Y. Abe, T. Inami, Y. Kawamura and Y. Koyama, *Radion stabilization in the presence of Wilson line phase*, PTEP 2014 073B04, DOI 10.1093/ptep/ptu097, original physical model for free 5D KK periodic radion/Wilson determinants.
- DASHI [#1094](https://github.com/chboishabba/dashi_agda/pull/1094) 243=3+240 ternary only (NOT E8 roots); [#701](https://github.com/chboishabba/dashi_agda/pull/701) ideal conducting-plate 720→240 (NOT 5D KK source); [#1248](https://github.com/chboishabba/dashi_agda/pull/1248) 1+1 optical Dirac loop Casimir (NOT 5D compactification).
- Existing actual gauge/Higgs/SM owner imports include `GaugeSingletPortal.agda`, `HiggsElectroweakBoundary.agda`, `U1YChargeAssignmentTableReceipt.agda` and `AnomalyCancellationVerificationReceipt.agda`. A singlet interaction being allowed does not supply a physical coupling/action/mass spectrum.
- Existing [Lean TOE #80](https://github.com/chboishabba/dashi_lean4/pull/80), [Lean crossprover #84](https://github.com/chboishabba/dashi_lean4/pull/84) and [Agda TOE #1217](https://github.com/chboishabba/dashi_agda/pull/1217) own physical common-action/stress and source-grade rules, not a constructed E6 grand unified model.

## Exact conditional field-spectrum calculation

Choose periodic 5D S1 radius b, reference b0=10^-24 m, 4D independent Maxwell photon B_mu, vanishing classical scalar condensates and the previously scoped electron Casimir-stabilized content:
- graviton + independent Maxwell + neutral real scalar: -9 free periodic polarisation units;
- three massive neutral 5D Dirac fermions: +12;
- one massive Maxwell-unit-charged Dirac: +4;
- four massive Maxwell-unit-charged complex scalars: -8;
- one free electron-mass Dirac zero-mode: +4 (me=0.00051099895 GeV INPUT);
- SU3_colour eight massless 5D gluons: -24;
- six light colour-triplet vectorlike 5D Dirac quarks: +72, with PHYSICAL charges u,c,t +2/3; d,s,b -1/3 under the independent electromagnetic B_mu;
- TWO extra **UNBROKEN, MASSLESS** SU3 octet gauge sectors: -48 (16 vectors × THREE massless 5D polarizations). This is a CONDITIONAL group-structured donor inspired by E6⊃SU3³. No physical E6 breaking potential or additional matter representations are supplied.

Define `f(s,theta)=Re[Li5(e^{-s+i theta})+s Li4(e^{-s+i theta})+(s²/3)Li3(e^{-s+i theta})]/ζ(5)`; x=b/b0, z=2πm_N b0, ze=2πme b0, z_q=2πm_q b0. The exact selected *free one-loop* Einstein-frame dimensionless potential is

`U(x,theta)=ell/x+W(x,theta)/x^6`,

`W(x,theta)= -81 + 12f(zx,0) +4f(4zx,theta)-8f(zx,theta)+4f(ze x,theta)+12 Σ_{q in u,d,s,c,b,t} f(z_q x, Q_q theta)`.

The `-81=-9-24-48` includes two hidden massless SU3 vector factors. Charges multiply Wilson phase as q theta. The scalar of the original portal owner would be *Q_EM-neutral*, so it contributes to W(x,0) but **not** to d²W/dtheta² for fixed mass, absent condensate/mixing/interactions.

## Positive result: selected radion stationary vacuum can be retuned

With `ell=-W(1,0)`, stationary radius requires `W_x'(1,0)-5W(1,0)=0`. The root shifts from the original QED-only z=**0.9081569907830750** to z=**0.9081569907706790**, a change of -1.2396×10^-11. It gives
- tuned ell≈**0.5960733250078880**;
- radion U_xx≈**+15.3940431522419**;
- zero 4D vacuum energy by explicit counterterm tuning.

This is an actual selected **local radial** solution at the declared free-field level, stronger than merely matching 48 counts. It is not evidence that E6 grand unification, light dark gauge bosons or material Earth physics is realized.

## Decisive failure: the same quarks destroy the electromagnetic Wilson vacuum

At zero Wilson phase and the retuned radial minimum:
- previous electron/heavy-charged sector `U_theta theta(QED) ≈ +1.99587282944639`;
- six quarks with 3 colours each, correct electric charges `U_theta theta(quarks) = 12 Σ Q_q² f_theta theta(z_q,0) ≈ -23.18496919730197`;
- **TOTAL** `U_theta theta ≈ -21.18909636785557 < 0`.

The quark signs are not optional: `Σ_q Q_q²=5/3` and `f_theta theta(0,0)=−ζ(3)/ζ(5)`; thus the massless-quark asymptotic is `12(5/3)×(−ζ3/ζ5)≈−23.18497`. The Hessian at (x=1,theta=0) is a **saddle**, not the claimed stable compactification. This kills the *joint* QED+QCD+radion/Wilson consumer despite a positive radial Hessian.

A nonzero O(1) Wilson phase would generally lift the formerly light periodic charged 4D fermion KK zero modes by ∼Q theta/(2πb0). Keeping the electron momentum shift below its input mass requires `|theta|≲2πme b0≈1.6271×10^-11`. So moving to a distant Wilson minimum is not a costless physical fix.

## Quantified restricted charged-matter repair and vector-polarization correction

A periodic uncondensed **neutral Higgs portal singlet** contributes ZERO direct Wilson phase curvature, even with arbitrarily many such completely U1-neutral fields at this free-field order. It cannot fix the negative Utheta-theta.

For an *idealised* free, uncondensed, massless **unit-charge charged scalar degree** (one real polarization counted within a COMPLEX U1 representation), the maximum positive Wilson Hessian contribution is `ζ(3)/ζ(5)≈1.15925`. The selected deficit 21.1891 therefore requires at least **19 real charged polarization units**, i.e. **10 additional charged complex scalar multiplets** in this especially restrictive q=1 free boson class. This is a **Wilson-consumer-only** bound, NOT a joint repair: those charged bosons also change W and its radial stationarity by up to ~100 units, so the radial equation must be re-solved. Larger EM charges, different boundary conditions, background vevs, interactions and gauge fields alter the model and require new same-action checks.

CORRECTION to the earlier 86.3077-GeV vector-mass shorthand: 16 extra 5D **MASSLESS GAUGE** vectors contribute 16×3=48 polarizations, but 16 ordinary **5D Higgsed/Proca MASSIVE** vectors would have 16×4=64 physical polarizations, with additional source Higgs/ghost/goldstone contributions. It is INVALID to assign the previous 48-unit scalar free determinant a physical massive SU3 vector mass of 86 GeV without deriving and counting the actual broken gauge sector. A Wilson-holonomy generated 4D vector mass within locally massless 5D gauge fields may keep 3 5D polarizations but shifts full gauge/matter KK spectra and cannot make all SU3 generators uniformly massive in a generic flat Wilson background. The old 86.3077 number is **only an effective 48-scalar-like-unit tuning parameter**, not a physical gauge boson mass prediction.

## Updated BIDI / Pareto priorities

1. A physically specified QED+QCD+EW/E6 source needs BOTH D=0 (radion) and nonnegative full Wilson/Higgs Hessian on the SAME field content. The new massless-vector E6-inspired candidate passes the first and FAILS the second.
2. Need a source-derived charged bosonic/gauge/Higgs spectrum to repair the Wilson angle while retaining light quark/electron and not making a new radial/5D pressure imbalance. *At least 10 ideal unit-charge complex scalar multiplets* is a restricted lower bound, NOT the preferred physical solution.
3. With compatible action and spectrum, derive the actual 5D stress including conserved quark/nuclear sources and Einstein metric variation; then rotating Earth and LARES. Current nodal proxies remain conditional/mostly GR-like.
4. Distinct 240 graph roles, the #1248 wormhole optical loop, #701 plates, horns and 27/729 cardinalities are NOT source predicates for this local physical KK action.
5. No SM chirality, E6 breaking, lattice continuum determinant, interacting nonabelian QCD Casimir, collider viable extra sectors, Agda/Lean kernel or measured gravitational anomaly are established.

## Verification

Independent local mpmath calculation using the identical free spectral functions and charges: PASS stationary radial equations, Uxx positive, Utheta-theta negative, 19/10 charged-boson bound. The new GitHub Python file is committed and source-verified; exact-head GitHub blob has NOT been byte-replayed in a local repo checkout. No Agda exact-head typecheck. Original literature and source-branch attributions preserved.
