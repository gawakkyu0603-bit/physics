# Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity

**KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions**

Yohtaro Soga · 27 November 2026

This is the second study in the [OSTQD research series](../observer-separated-two-time-quantum-dynamics/README.md). It explicitly relaxes the preceding paper's strict subsystem energy-moment immunity for reduced thermal open systems. Its low-energy models are conditional and their physical completions remain open.

## Results and scope

| Result | Exact scope and material |
| --- | --- |
| **Fixed-temperature KMS covariance** | Eigenoperator jumps preserve two-time commutation despite energy exchange; detailed balance gives symmetric GNS decay. Time-dependent holonomy and Gibbs tracking require different controls. [Theorem 1 and Proposition 1](v1/paper/main.pdf), [Lean source](v1/lean4/OSTQD_SK/Theorem1_CovariantKMS.lean). |
| **JT fluctuations** | The frozen-coefficient linearized Bernard–Doyon closure has explicit cumulants for every order n≥2. State-dependent feedback changes the leading third cumulant. Three equilibrium closures with fixed drift give fourth-cumulant ratios 0.5, 1.5, 1.0. [Theorem 2 and Proposition 2](v1/paper/main.pdf), [Lean source](v1/lean4/OSTQD_SK/Theorem2_WardAndFDT.lean). |
| **Smooth-band chiral-horizon obstruction** | For nonzero smooth compactly supported number dephasing on the specified free chiral field, the raw tempered defect is non-Hadamard and its UV-finite raw detector response turns negative at large gap. Any positive-type finite-order point-contact extension requires a strictly positive contact coefficient and a high-gap floor. This does not establish existence of a global positive state. [Theorem 3 and Propositions 3–4](v1/paper/main.pdf), [Lean source](v1/lean4/OSTQD_SK/Theorem3_HorizonHadamard.lean). |
| **Thermal ports, greybody scattering, and channel erasure** | Per-port KMS locking, fixed-frequency static Schwarzschild asymptotics, exact replacer fidelity and separate finite models identify conditional restrictions, not a common gravitational endpoint. [Theorem 4 and Proposition 5](v1/paper/main.pdf), [Lean source](v1/lean4/OSTQD_SK/Theorem4_NonIsometricThroat.lean). |

[Manuscript (PDF)](v1/paper/main.pdf) · [Research materials](v1/README.md) · [Relation to prior literature](v1/PRIOR_ART.md) · [Mathematical and numerical verification scope](v1/VERIFICATION.md)

## English reading guides

[General readers](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd-sk-jt/general.html) · [STEM students and graduates](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd-sk-jt/student.html) · [Specialists](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd-sk-jt/expert.html)

The preceding study is [Observer-Separated Two-Time Quantum Dynamics](../observer-separated-two-time-quantum-dynamics/README.md). Established open-system, gravity and quantum-information results are credited in the manuscript. The central new constructions are conditional analytic additions, not a derivation of microscopic gravity or a completed observer-separated instrument model.
