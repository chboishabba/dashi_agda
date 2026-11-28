# J22 — native-source hybrid monodromy, loaded-port matching and numerical shooting

**23 November 2026 | PR #1537 | synthetic driver-OFF, prescribed-wave-ON Filsinger S3/HF receiver consumer.** Uses the original J12/J18/J19/J20 nine-state model and J21 point, with original Smith/Filsinger credit retained. No original pin map, measured naturally available wave, source-to-device transfer, superconducting return, or gravity mechanism established.

## Important execution distinction

Independent local **NumPy/SciPy** implementation of the J18 nine-state equations was executed, including the analytical nine-by-nine piecewise variational Jacobian, jump/saltation matrices for all spark events, Poincare shooting correction, tighter numerical energy replay and finite-difference controls. It reproduces the prior J21 nine-state operating point. The new [J22 native-source executable](../../scripts/check_smith_filsinger_j22_saltation_shooting_20261123.py) has been **committed** and reads the actual unchanged J18/J19/J20/J21 Python owners by import and source hash. **The committed J22 file has NOT yet been locally executed byte-for-byte with those native owners.** This is an OPEN native acceptance gate, not a claim of completed original-source acceptance. No GitHub Actions, CI or Agda kernel.

Source blobs pinned: J12 f5f66e343a979dfe2bc70f68e1e98fce75817653; J18 f4270a475f010874056cfe3cdeff5ee8e43c44eb; J19 cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439; J20 ed09b82287ec1ca0318b4f8e9d355f614d00d894; J21 b4c865f465f1a4a2e8dd40820eb02a6456454d67.

## Exact hybrid mathematics; numerical values conditional on the model

Let x=(i,j,u,v,b,q,r,i_h,x_h) be the nine-state vector. On each fixed spark state chi, the original nonlinear differential equation is dx/dt=f_chi(t,x). The diode currents remain ju=max((u-b-Vd)/Rd,0) and jv=max((v-b-Vd)/Rd,0), with their almost-everywhere derivative on smooth segments. At each bank threshold g(x)=b-Vthreshold=0, the state has no reset but the vector field changes from f_minus to f_plus. With normal n=e_b and strictly transverse pre-switch crossing, the **saltation operator** is

    S=I + (f_plus-f_minus) n^T/(n^T f_minus).

Compose the smooth tangent flows with all 22 saltation updates to get the one-period return-map derivative M. This corrects the earlier false inference that matching event counts suffices. The native work channels are unaffected by tangent instrumentation. The finite capacitor and positive coil/gap losses remain in force.

At the selected J21 point gamma_i=0.0002, gamma_r=0.015, k=0.35, kh=2, Gload=0.52, driver OFF and source_amp=1.2, all 22 observed threshold crossings have positive direction-corrected bank slope. The smallest is **0.0920361**; the closest successive event-time separation is **0.0240478** model-time units. Piecewise RHS Jacobians independently match centred numerical RHS derivatives to about **2.6e-9 absolute max** at the sampled state.

| Hybrid return-map numerical check | Value |
| --- | ---: |
| Spectral radius rho(M) | 0.27108218 |
| sigma_min(I-M) | 0.80728379 |
| Condition number(I-M) | 1.26058888 |
| M relative change between rtol 3e-8 and 3e-10 | 2.32e-6 |
| M versus independent centred direct state-map FD at h=1e-3 | 2.45e-5 relative |
| M versus FD at h=3e-4 | 6.46e-5 relative |
| M versus FD at h=1e-4 | 1.66e-4 relative |

A previous 1e-5/5e-6 finite-difference test with coarse ODE tolerance produced a ~0.989 relative difference and must **NOT** be used as a derivative certificate. Refining time integration and using analytic tangent plus event-time saltation removes that unstable interpretation. No interval/event-separation proof holds over a nonzero parameter box yet; numerical contraction at a candidate fixed point is not a computer-assisted proof.

## Shooting Newton correction and tightened work ledger

Using F(x)=flow_T(x) and Jacobian M, solve (I-M) delta=F(x)-x and take x_new=x+delta. A single correction in the independent high-accuracy tangent solver changed max-norm return-map residual **1.7421173e-6 → 1.403322e-13** while retaining the 22 events and nonzero transversality.

Independent strict-tolerance work-integrating ODE replay (rtol 3e-11, atol 3e-13) at the corrected state:

| Work / acceptance | Result |
| --- | ---: |
| Incident wave | 90.4778684234 |
| Outgoing wave | 31.0579347887 |
| HF-load work | 46.5616595586 |
| Net wave captured | 59.4199336347 |
| Field heat | 1.6460778537 |
| HF gap / coil heat | 2.7936127405 / 1.5524691520 |
| Copper1 / copper2 | 0.2870489570 / 2.6275411344 |
| Diode / bleed heat | 0.4031753050 / 3.5483489340 |
| Driver input | 0 |
| Total storage drift | -8.5080e-10 |
| Signed full energy residual | +4.7444e-10 |
| Cycle state closure (independent work solver) | 1.6081e-9 |
| Source-only incident-to-load ratio | **51.4619324813%** |
| Net wave capture | **65.6734455289%** |

The ratio is *mathematically attributable to the model's independently imposed wave port* only because driver=0 and the restored work identity is enforced. This is not natural source measurement. In particular, the original FM physical pin role evidence remains 0/4 and original measured work roles 0/24.

## Actual selected-branch radiative sweep

The independent locally executed warm continuation used up to 15 cycles with strict original J19 restoration, event labeling, closure, energy and event-time gates. Only rows explicitly marked with 22 events belong to the target branch.

| gamma_rad | load / incident | 22 events? | min signed crossing slope |
| --- | ---: | --- | ---: |
| 0.010 | 49.23534% | yes | 0.06499 |
| 0.012 | 50.82230% | yes | 0.08029 |
| 0.014 | 51.42395% | yes | 0.08931 |
| 0.015 | 51.46193% | yes | 0.09204 |
| 0.016 | 51.36734% | yes | 0.09385 |
| 0.018 | 50.87648% | yes | 0.09566 |
| 0.020 | 50.10431% | yes | 0.09607 |
| 0.023 | 48.63727% | yes | 0.09608 |

A finite local peak is apparent near 0.015, with a Pareto trade-off between useful load and event-crossing slope. The 0.008 point did not meet the bounded convergence gate; no absence-of-solution inference. At Gload=0.54, the independent model restores with **zero spark events**, despite positive load; at kh=2.025, the event count is **44**, and at kh=2.005 the finite continuation alternated between 32 and 34 switches without restoration. **Do not optimize across those event branches** or call them 22-event successors.

## Exact obstruction and remaining gates

The J21 nonlinear capacitor on a restored HF cycle obeys integral(x_h i_h)=Gload integral(x_h²); by Cauchy–Schwarz, Wcoil >= Rcoil Gload Wload. Thus even on a perfect wave-matched boundary the present finite-resistance circuit obeys eta_source-to-load <=1/(1+Rcoil Gload)<1 at positive load. Other outgoing, heat, diode and bank losses make the observed ratio lower.

Next J23 obligation: (1) byte-exact run of committed J22 checker on the original native owners, with hash acceptance; (2) interval enclosure of a true Poincare fixed point and its saltation/event margins; (3) construct a nonzero same-event-branch parameter box with signed interval/range checks and branch-aware Pareto solution; (4) original source and device physical calibration, including source polarization/phase, wave port and original terminal and load energy. No theorem about ambient RF harvesting or exotic gravity is claimed.

