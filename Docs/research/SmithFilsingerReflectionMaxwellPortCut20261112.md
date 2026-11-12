# Smith–Filsinger reflected-wave and Maxwell port maximum cut (12 November 2026)

## Original source and identity
User-supplied Kelly/Darrer 147-page Smith compilation pp48–51: 1:4 **wire-length** rule, movable primary, split secondaries; pp80–82: two out-of-phase described L2 branches, diodes and multiple grounds. No source-measured 90° secondary **current** phase or energy multiplication; do not translate physical winding angle into electrical phase. The ZVS driver in Filsinger's reel is a **replaceable driver technology**, not the canonical device. Distinct Earth-ground and *proposed* portable golden 1:1.618 antenna configurations stay separate.

## New physically grounded reflection owners
A local reproducible package `smith_filsinger_reflection_maxcut.zip` executed **30/30 Python tests PASS** without CI.

**Electrical transformer reflection:** linear tuned multiple-secondary test includes `Z_reflected = N (omega M)^2 / Z_secondary` for selected real tuned impedances. Additional loaded secondaries alter driver impedance; secondary-secondary coupling and parasitics still unmodelled.

**Open port reradiation:** energy-conserving multi-mode TCMT with `da/dt=(iH-Di-Dl-BB†/2)a+B s_plus`, `s_minus=-s_plus+B†a`, using reciprocal external radiation coupling and separate EM/driver ports. Explicit `P_incident = Σ P_outgoing + P_load + P_internal` tested for either and both source ports, including conservative nonlinear detuning. This is a **finite modal model**; original-specific B is OPEN. For one mode external .04, intrinsic .02, load .02: reflection 0, useful .5, internal .5. For load .06: reflection 1/9, useful 2/3, internal 2/9. **Zero reflection is distinct from maximum useful extraction**.

**Actual open Maxwell field reference:** Hertzian *infinitesimal electric dipole*, uniform prescribed current, outgoing far-zone `E_theta=i Z0 k I_rms l sin(theta) exp(-ikr)/(4pi r)`, `H_phi=E_theta/Z0`. Integrate radial Poynting flux: `R_rad=(2pi Z0/3)(l/lambda)^2`, approximately `80pi²(l/lambda)²`. Radiative energy flux and inverse scattering are represented for **this ideal antenna only**. A finite loaded golden plate is not this dipole and remains open.

**Nonlinear coefficient cut:** source-free closed PEC rectangular TMz eigenfunctions (1,2)/(2,1) at phi:1 produce normalized spatial overlap integrals `∫u12⁴=∫u21⁴=1.39057647`, `∫u12²u21²=0.61803399`; exact mode normalizations and orthogonality tested. These establish **geometry factors**, not physical nonlinear coupling coefficients: conductivity, material χ^(3), field scaling, nonlinear core/switch, radiative modes and energy-normalization coefficients remain unselected. Numerical reciprocal four-wave Hamiltonian derivative and source-off energy invariance passed.

## Source-faithful transformations
Partial typed-source graph JSON separately represents Smith suitcase Figure 10, Filsinger's Earth-reel candidate, and his *proposed* portable midpoint+plate. One narrated connection white capacitor **hot→Earth-negative** is retained; no blue capacitor, green rectifier, hidden resistor or meter-terminal physical connection is invented. Transformation **removes** narrated Earth edge and **adds a proposed** antenna→midpoint edge but explicitly sets `equivalent_electrical_behavior=false`.

## Maximum cut remaining — not claimed complete
P0: original terminal netlists and actual Filsinger board/bridge; electrical clock vs 7.8kHz acoustic line.
P1: full *open finite-conductivity golden rectangle* Maxwell with material/dimensions/feed/ground and Poynting flux; actual nonlinear coefficients from same physical modes.
P1: measured signed environmental port work (Earth chemistry/geoelectric, atmosphere, ambient RF, ionising radiation) after all drive/storage/load/heat terms.
P2: actual Agda 2.9 kernel verification of new finite/source BIDI and selected same-object physically coupled equations. Python tests do not constitute source measurements.

The hypothetical Smith 8kV×20A is **160kVA**, not automatically 160kW; 159,988W deficit requires the additional assumption of 160kW real sustained output and 12W real input.
