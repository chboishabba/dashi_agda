# Smith / Filsinger original PDF: quadrature cascade and nonlinear single-wave receiver (2026-11-12)

## Actual PDF answer before modelling
The user-supplied 147-page Kelly/Darrer compilation says Smith prescribed an **L1:L2 winding wire length of 1:4** (pp48–51), with two **17-turn secondary sections**, an illustrative **5⅔ turns and 240-degree mechanical angular endpoint displacement**, movable transformer coupling, and tuning capacitors. **Do not interpret the wire-length ratio or mechanical angle as measured electric phase.** pp80–82 Figs 53–55 discuss out-of-phase/opposed secondary voltages, diode combining and two distinct Earth grounds. They do not explicitly establish a 90-degree stage-to-stage current quadrature cascade, an independently powered stage or a golden-ratio source geometry.

The more defensible physical steelman is: sinusoidal changing magnetic flux gives transformer induced EMF in quadrature with FLUX via Faraday's law, but current phase depends on complex load; coupled stages reflect their impedance to their source. Filsinger's separate proposed 1:1.618 rectangle could produce orthogonal mode phase splitting under a single coherent incident plane wave and **appropriate reactive loading**, but the ratio alone does not impose 90 degrees.

## New executable nonlinear model and precise admitted limits
Local archive `/mnt/data/smith_filsinger_nonlinear.zip` contains:
- `model.py` / 12/12 standard-numerical assertions PASS: single coherent incident wave with orthogonal projections, geometry-dependent detuning, reciprocal coupling, Kerr reactive detuning, source-work and dissipative-load accounting; rectangular stream-function **scalar Dirichlet Laplace** current proxy tests.
- `mixing.py` / 6/6 mathematical tests PASS: conservative nonlinear four-wave-mixing stage `i*mu*conj(ax)*ay²`, and symmetric term `i*mu*conj(ay)*ax²`. The terms exchange energy between modes while obeying `dU/dt = 2 Re(a†b) − 2 gamma U` and cannot themselves generate energy. A large brute-force search was aborted; no globally certified optimisation.
- `fixed_phi_fast.py`: 2,200-seeded-point parameter scan at a **fixed** rectangle ratio φ with steady-state root and time-domain revalidation. The selected points follow:
  - linear maximum found useful power .6101, abs circularity .3414;
  - nonlinear maximum found useful power .6276, circularity .0743;
  - linear circulation-reward selected useful power .4906, abs circularity .8429;
  - nonlinear circulation-reward selected useful power .4961, abs circularity .8141.
This demonstrates that circulation and useful power are not synonymous and that nonlinear mixing admits additional phase-dependent operating points. The slight best-of-random-scan differences do NOT demonstrate a universal nonlinear improvement or physical energy gain (different random parameter points, and physical overlap coefficients unconstrained).

Energy source = ONE coherent external mode feed with two projections, input ||s||²=1. Radiation/earth/electrochemistry/particle input remains unmeasured. All output useful-power fractions are synthetic normalized values, NOT measured W, capture efficiency or actual antenna field solutions.

## Maxwell bridge: what is and is not paid
Scalar rectangular Dirichlet eigenfunctions `sin(mπx/a)sin(nπy/b)` satisfy a 2D Helmholtz scalar eigenproblem with `k²=π²[(m/a)²+(n/b)²]`. `J=(-∂yψ,∂xψ)` is divergence-free and tangential on boundaries for `ψ=0` there. A nonzero curl of this **constructed stream-current** is not the same as showing a current distribution solving actual Maxwell vector equations and conductor surface impedance, nor as proving source-driven resonant trapped circulation. This supplies a sound analytic test field and negative controls for the existing Agda Maxwell source/PEC BIDI owners; the FULL physical Maxwell-source/geometry weld is OPEN.

## Source-grounded next actual work
P0 full selected Smith figure 28/53–55 port/pin transcription and Filsinger hardware mapping; distinguish later reel occasions and user-identified three blue capacitors/green rectifier candidates.
P1 material-defined Maxwell finite conductor and counterpoise boundary, actual incident-field and feed distribution; compute physical overlap `kappa,chi,mu`, radiation damping and Poynting input.
P1 nonlinear device and shunt-current frequency-pulling from 1/2/4 MΩ values, including actual switching frequency (not microphone proxy), loaded feedback and real cost of active tuning.
P1 live Earth, atmospheric, RF, cosmic particle and driven ports, real-power/energy receipts under null controls. Global Schumann frequency not promoted from approximate 7.8kHz acoustic ratio.
P2 same-revision Agda 2.9/Nix check; this new work is **local Python**, not an accepted Agda theorem.

## Attribution
Don Smith original as compiled by Patrick Kelly/Brendan Darrer = historical claims; Filsinger reels = modern reported apparatus and proposed portable modification; nonlinear mixing and Maxwell proxies = independent mathematical steelman authored for this investigation. No original claim of independent excess energy is marked physically verified.
