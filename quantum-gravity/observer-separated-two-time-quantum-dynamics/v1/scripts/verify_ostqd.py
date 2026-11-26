#!/usr/bin/env python3
"""
Numerical verification and figure generation for:
  Observer-Separated Two-Time Quantum Dynamics (OSTQD)

Verifies Theorems 1-5 and boundary/counterexample checks to machine precision,
and simulates:
  1. Theorem 1: Carre du champ identity, exact variance-derivative decomposition,
     eigenbasis-averaged initial variance rate, maximally-mixed drift-cancellation
     example, nonzero-drift zero-covariance example, and non-commuting (t,s) PDE check.
  2. Theorem 2: 2-level Bogoliubov incompatibility, exact 4D fermionic Hawking pair
     ([H_A, H_B] = 0 on M_4(C), exterior-local incompatibility
      gamma_loc = 8 omega^2 n_FD (1 - n_FD), exact GKSL ODE trajectory, and
      linear-entropy saturation identity), proportional-redshift dephasing example,
     general non-unital GKSL expectation-preservation check, and truncated bosonic
     Fock-space heating rate.
  3. Theorem 3: P_A P_B P_A = d^{-2} P_A, sharp linear sum bound F_A + F_B <= 1 + 1/d,
     valid CPTP Choi saturation state sigma_* (marginal Tr_{A'B'} sigma_* = I_R / d),
     Kay-Kaszlikowski-Ramanathan (2009) curved monogamy boundary check, and explicit
     inverse-decoder entanglement fidelity + CPL check.
  4. Theorem 4 & Unified Two-Window N=8-Qubit Evaporation Model:
     Piecewise time-dependent unitary driving inside a finite-width two-window space
     H_tot = H_win1 (+) H_win2 with coarse-grained jump K_B = E1 Pi_1 + E2 Pi_2
     satisfying [K_B, H_dyn(t)] = 0 at all steps, non-trivial intra-window t-scrambling,
     exact s-invariance across the entire k = 0..8 Page curve & Petz recovery trajectory
     (verified with exact partial trace rho_win1 = psi^T psi^*), and exact exponential
     inter-window dephasing linking lim_{s->inf} e^{s L_B} = P_win.
  5. Theorem 5: Intermediate-dimension bottleneck bound F_e <= min(1, d_f^2 / d_C^2)
     with encoder Kraus count k_enc = max(2, ceil(d_C / d_f)) and strict shape &
     trace-preservation assertions across all 1,500 random trials.
  6. Independent Companion Matrix-Model Benchmark:
     True Galerkin projection of the SU(2) 2-matrix bosonic Yang-Mills polynomial
     Hamiltonian (built at intermediate cutoff 5 and verified against cutoff 6,
     projected onto the 84D cutoff-3 space and 4D exact SO(3) singlet sector).

Outputs:
  - docs/numerical_verification.json
  - paper/figures/fig1_horizon_heating.pdf
  - paper/figures/fig2_joint_vs_separated.pdf
  - paper/figures/fig3_matrix_evaporation.pdf
"""
from __future__ import annotations

import itertools
import json
import math
import platform
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import scipy
import scipy.sparse as sp
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parent.parent
FIG_DIR = ROOT / "paper" / "figures"
DATA_DIR = ROOT / "docs"
FIG_DIR.mkdir(parents=True, exist_ok=True)
DATA_DIR.mkdir(parents=True, exist_ok=True)

SEED = 20261126
FLOAT_TOL = 1e-12
rng = np.random.default_rng(SEED)


def comm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return A @ B - B @ A


def dag(A: np.ndarray) -> np.ndarray:
    return A.conj().T


def frob_sq(A: np.ndarray) -> float:
    return float(np.real(np.trace(dag(A) @ A)))


def gksl(rho: np.ndarray, Ls: list[np.ndarray]) -> np.ndarray:
    out = np.zeros_like(rho, dtype=complex)
    for L in Ls:
        LdL = dag(L) @ L
        out += L @ rho @ dag(L) - 0.5 * (LdL @ rho + rho @ LdL)
    return out


def gksl_dual(X: np.ndarray, Ls: list[np.ndarray]) -> np.ndarray:
    out = np.zeros_like(X, dtype=complex)
    for L in Ls:
        LdL = dag(L) @ L
        out += dag(L) @ X @ L - 0.5 * (LdL @ X + X @ LdL)
    return out


def gksl_flow(rho: np.ndarray, Ls: list[np.ndarray], s: float) -> np.ndarray:
    d = rho.shape[0]
    L_super = np.zeros((d * d, d * d), dtype=complex)
    for idx in range(d * d):
        E = np.zeros((d, d), dtype=complex)
        E.flat[idx] = 1.0
        L_super[:, idx] = gksl(E, Ls).reshape(-1)
    return (expm(s * L_super) @ rho.reshape(-1)).reshape(d, d)


def vn_entropy(rho: np.ndarray) -> float:
    vals = np.linalg.eigvalsh(0.5 * (rho + dag(rho)))
    vals = vals[vals > 1e-15]
    return float(-np.sum(vals * np.log(vals)))


def linear_entropy(rho: np.ndarray) -> float:
    return float(1.0 - np.real(np.trace(rho @ rho)))


def kay_curved_bound(fa: np.ndarray | float, d: int) -> np.ndarray | float:
    """Exact curved singlet-monogamy / cloning bound (Kay et al., PRL 103, 050501, 2009)."""
    return (np.sqrt(fa) / d + np.sqrt(1.0 - 1.0 / (d * d)) * np.sqrt(np.maximum(0.0, 1.0 - fa))) ** 2


# ==============================================================================
# 1. VERIFY THEOREM 1 (Carre du champ, Variance Decomp, BPS & Drift Audits)
# ==============================================================================
def verify_theorem_1() -> dict:
    max_id_err = 0.0
    max_comm_err = 0.0
    max_var_decomp_err = 0.0
    max_eigenstate_var_err = 0.0
    max_eigenbasis_avg_err = 0.0

    for d in [2, 4, 6]:
        A = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        H = 0.5 * (A + dag(A))
        Ls = [rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for _ in range(3)]

        D = gksl_dual(H, Ls)
        Gamma_op = gksl_dual(H @ H, Ls) - H @ D - D @ H
        rhs = sum(dag(comm(L, H)) @ comm(L, H) for L in Ls)
        max_id_err = max(max_id_err, float(np.linalg.norm(Gamma_op - rhs)))

        # Random state check of exact variance-derivative decomposition:
        # d/ds Var_rho(H) = <Gamma(H,H)> + <H D + D H> - 2 <H><D>
        R = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        rho = dag(R) @ R
        rho /= np.trace(rho)
        var_deriv_direct = float(np.real(
            np.trace(gksl_dual(H @ H, Ls) @ rho)
            - 2.0 * np.trace(H @ rho) * np.trace(D @ rho)
        ))
        var_deriv_decomp = float(np.real(
            np.trace(Gamma_op @ rho)
            + np.trace((H @ D + D @ H) @ rho)
            - 2.0 * np.trace(H @ rho) * np.trace(D @ rho)
        ))
        max_var_decomp_err = max(max_var_decomp_err, abs(var_deriv_direct - var_deriv_decomp))

        # Exact eigenstate variance derivative = <E_j | Gamma(H,H) | E_j>
        # and eigenbasis average = (1/d) Tr(Gamma(H,H))
        evals, evecs = np.linalg.eigh(H)
        eig_var_sum = 0.0
        for j in range(d):
            v = evecs[:, j]
            rho_j = np.outer(v, v.conj())
            vd_j = float(np.real(
                np.trace(gksl_dual(H @ H, Ls) @ rho_j)
                - 2.0 * np.trace(H @ rho_j) * np.trace(D @ rho_j)
            ))
            gam_j = float(np.real(np.trace(Gamma_op @ rho_j)))
            max_eigenstate_var_err = max(max_eigenstate_var_err, abs(vd_j - gam_j))
            eig_var_sum += vd_j
        avg_trace = float(np.real(np.trace(Gamma_op))) / d
        max_eigenbasis_avg_err = max(max_eigenbasis_avg_err, abs(eig_var_sum / d - avg_trace))

        # Construct H-commuting jump operators via eigenbasis of H
        Ls_comm = []
        for _ in range(3):
            diag_c = rng.normal(size=d) + 1j * rng.normal(size=d)
            Ls_comm.append(evecs @ np.diag(diag_c) @ dag(evecs))
        err1 = float(np.linalg.norm(gksl_dual(H, Ls_comm)))
        err2 = float(np.linalg.norm(gksl_dual(H @ H, Ls_comm)))
        err3 = float(np.linalg.norm(gksl(comm(H, rho), Ls_comm) - comm(H, gksl(rho, Ls_comm))))
        max_comm_err = max(max_comm_err, err1, err2, err3)

    # Maximally-mixed drift-cancellation example: H_A = sigma_x, H_B = sigma_z, L = sigma_z, rho_mm = I/2
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sz = np.array([[1, 0], [0, -1]], dtype=complex)
    rho_mm = 0.5 * np.eye(2, dtype=complex)
    D_ce = gksl_dual(sx, [sz])
    Gam_ce = gksl_dual(sx @ sx, [sz]) - sx @ D_ce - D_ce @ sx
    mm_rho_deriv = float(np.linalg.norm(gksl(rho_mm, [sz])))
    mm_var_deriv = float(np.real(
        np.trace(gksl_dual(sx @ sx, [sz]) @ rho_mm)
        - 2.0 * np.trace(sx @ rho_mm) * np.trace(D_ce @ rho_mm)
    ))
    mm_gamma_exp = float(np.real(np.trace(Gam_ce @ rho_mm)))
    mm_drift_cov = float(np.real(
        np.trace((sx @ D_ce + D_ce @ sx) @ rho_mm)
        - 2.0 * np.trace(sx @ rho_mm) * np.trace(D_ce @ rho_mm)
    ))
    # Eigenstates |+>, |-> of H_A = sigma_x
    plus = np.array([1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    minus = np.array([1.0, -1.0], dtype=complex) / math.sqrt(2.0)
    eig_rates = []
    for v in (plus, minus):
        rv = np.outer(v, v.conj())
        eig_rates.append(float(np.real(
            np.trace(gksl_dual(sx @ sx, [sz]) @ rv)
            - 2.0 * np.trace(sx @ rv) * np.trace(D_ce @ rv)
        )))
    mm_eig_avg = float(np.mean(eig_rates))
    assert abs(mm_rho_deriv) < FLOAT_TOL
    assert abs(mm_var_deriv) < FLOAT_TOL
    assert abs(mm_gamma_exp - 4.0) < FLOAT_TOL
    assert abs(mm_drift_cov + 4.0) < FLOAT_TOL
    assert abs(mm_eig_avg - 4.0) < FLOAT_TOL

    # Nonzero drift D != 0 with vanishing drift covariance on mixed state I_3 / 3
    H_r3 = np.diag([0.0, 1.0, 2.0]).astype(complex)
    L_r3 = np.zeros((3, 3), dtype=complex)
    L_r3[2, 1] = 1.0
    rho_r3 = np.eye(3, dtype=complex) / 3.0
    D_r3 = gksl_dual(H_r3, [L_r3])
    Gam_r3 = gksl_dual(H_r3 @ H_r3, [L_r3]) - H_r3 @ D_r3 - D_r3 @ H_r3
    r3_drift_cov = float(np.real(
        np.trace((H_r3 @ D_r3 + D_r3 @ H_r3) @ rho_r3)
        - 2.0 * np.trace(H_r3 @ rho_r3) * np.trace(D_r3 @ rho_r3)
    ))
    r3_var_rate = float(np.real(
        np.trace(gksl_dual(H_r3 @ H_r3, [L_r3]) @ rho_r3)
        - 2.0 * np.trace(H_r3 @ rho_r3) * np.trace(D_r3 @ rho_r3)
    ))
    r3_gamma_exp = float(np.real(np.trace(Gam_r3 @ rho_r3)))
    assert abs(float(np.linalg.norm(D_r3)) - 1.0) < FLOAT_TOL
    assert abs(r3_drift_cov) < FLOAT_TOL
    assert abs(r3_var_rate - 1.0 / 3.0) < FLOAT_TOL
    assert abs(r3_gamma_exp - 1.0 / 3.0) < FLOAT_TOL

    # Non-commuting (t,s) PDE integrability example: H = sigma_z, L = sigma_x, rho = |+><+|
    rho_plus = np.outer(plus, plus.conj())
    noncomm_pde_norm = float(np.linalg.norm(
        gksl(comm(sz, rho_plus), [sx]) - comm(sz, gksl(rho_plus, [sx]))
    ))
    assert abs(noncomm_pde_norm - 2.0 * math.sqrt(2.0)) < FLOAT_TOL

    return {
        "max_carre_du_champ_error": max_id_err,
        "max_bps_commutation_error": max_comm_err,
        "max_variance_decomposition_error": max_var_decomp_err,
        "max_eigenstate_variance_deriv_error": max_eigenstate_var_err,
        "max_eigenbasis_avg_variance_error": max_eigenbasis_avg_err,
        "variance_drift_cancellation_rho_mm": {
            "rho_mm_deriv_norm": mm_rho_deriv,
            "rho_mm_actual_var_deriv": mm_var_deriv,
            "rho_mm_carre_du_champ": mm_gamma_exp,
            "rho_mm_drift_cancellation": mm_drift_cov,
            "eigenbasis_avg_initial_var_deriv": mm_eig_avg,
        },
        "nonzero_D_zero_covariance_example": {
            "D_frobenius_norm": float(np.linalg.norm(D_r3)),
            "drift_covariance": r3_drift_cov,
            "actual_var_deriv": r3_var_rate,
            "carre_du_champ_expectation": r3_gamma_exp,
        },
        "noncommuting_pde_example": {
            "L_adH_minus_adH_L_frob_norm": noncomm_pde_norm,
            "exact_2_sqrt_2": 2.0 * math.sqrt(2.0),
        },
    }


# ==============================================================================
# 2. VERIFY THEOREM 2 (Local Horizon Incompatibility, Fermionic 4D & Bosonic)
# ==============================================================================
def verify_theorem_2() -> dict:
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sz = np.array([[1, 0], [0, -1]], dtype=complex)
    I2 = np.eye(2, dtype=complex)

    # (a) 2-level Bogoliubov exact gamma = omega^2 sin^2(theta)
    omega = 1.7
    max_2lvl_err = 0.0
    for theta in np.linspace(0.0, np.pi, 17):
        HB = 0.5 * omega * sz
        HA = 0.5 * omega * (math.cos(theta) * sz + math.sin(theta) * sx)
        X = (0.3 - 0.7j) * sz
        ratio = frob_sq(comm(X, HA)) / frob_sq(X)
        exact = (omega ** 2) * (math.sin(theta) ** 2)
        max_2lvl_err = max(max_2lvl_err, abs(ratio - exact))

    # (b) Exact 4D Fermionic Hawking pair (Jordan-Wigner representation)
    sm = np.array([[0, 1], [0, 0]], dtype=complex)
    bR = np.kron(sm, I2)
    bL = np.kron(sz, sm)
    NR = dag(bR) @ bR
    NL = dag(bL) @ bL

    max_ferm_err = 0.0
    max_ferm_hb_err = 0.0
    max_ferm_comm_HA_HB = 0.0
    max_ferm_gamma_loc_err = 0.0
    ferm_curves = {}
    Gamma = 1.0
    omega_h = 1.0

    # Bilocal vs exterior-local comparison at r = pi/6, omega = 1
    r_ref = math.pi / 6.0
    a1_ref = math.cos(r_ref) * bR - math.sin(r_ref) * dag(bL)
    a2_ref = math.cos(r_ref) * bL + math.sin(r_ref) * dag(bR)
    HA_ref = omega_h * (dag(a1_ref) @ a1_ref + dag(a2_ref) @ a2_ref)
    HB_ref = omega_h * (NR - NL)
    bilocal_comm_norm = float(np.linalg.norm(comm(HA_ref, HB_ref)))
    v_test = np.array([0.0, 1.0, 1.0, 0.0], dtype=complex) / math.sqrt(2.0)
    rho_test = np.outer(v_test, v_test.conj())
    bilocal_bps_res = max(
        float(np.linalg.norm(gksl_dual(op, [HB_ref])))
        for op in [HA_ref, HA_ref @ HA_ref, HB_ref, HB_ref @ HB_ref]
    )
    bilocal_nontrivial_sq = frob_sq(gksl(rho_test, [HB_ref]))
    gamma_loc_pi6 = frob_sq(comm(NR - 0.5 * np.eye(4), HA_ref)) / frob_sq(NR - 0.5 * np.eye(4))
    assert bilocal_comm_norm < FLOAT_TOL
    assert bilocal_bps_res < FLOAT_TOL
    assert abs(bilocal_nontrivial_sq - 2.0) < FLOAT_TOL
    assert abs(gamma_loc_pi6 - 1.5) < FLOAT_TOL

    for T_over_w in [0.1, 0.25, 0.5, 1.0, 2.0, 5.0]:
        r = math.atan(math.exp(-0.5 / T_over_w))
        n_FD = 1.0 / (math.exp(1.0 / T_over_w) + 1.0)
        assert abs(math.sin(r) ** 2 - n_FD) < 1e-14

        a1 = math.cos(r) * bR - math.sin(r) * dag(bL)
        a2 = math.cos(r) * bL + math.sin(r) * dag(bR)
        HA = omega_h * (dag(a1) @ a1 + dag(a2) @ a2)
        HB = omega_h * (NR - NL)

        # Verify [H_A, H_B] = 0 on M_4(C) and exact exterior-local gamma_loc
        max_ferm_comm_HA_HB = max(max_ferm_comm_HA_HB, float(np.linalg.norm(comm(HA, HB))))
        X_loc = NR - 0.5 * np.eye(4, dtype=complex)
        gamma_loc_num = frob_sq(comm(X_loc, HA)) / frob_sq(X_loc)
        gamma_loc_exact = 8.0 * (omega_h ** 2) * n_FD * (1.0 - n_FD)
        max_ferm_gamma_loc_err = max(max_ferm_gamma_loc_err, abs(gamma_loc_num - gamma_loc_exact))

        # Inertial vacuum |0_A> = cos r |00> + sin r |11>
        vac_B = np.array([1.0, 0.0, 0.0, 0.0], dtype=complex)
        vac_A = math.cos(r) * vac_B + math.sin(r) * (dag(bR) @ dag(bL) @ vac_B)
        assert np.linalg.norm(a1 @ vac_A) < 1e-14
        assert np.linalg.norm(a2 @ vac_A) < 1e-14
        rho0 = np.outer(vac_A, vac_A.conj())

        Ls_B = [math.sqrt(Gamma) * NR]
        max_ferm_hb_err = max(
            max_ferm_hb_err,
            float(np.linalg.norm(gksl_dual(HB, Ls_B))),
            float(np.linalg.norm(gksl_dual(HB @ HB, Ls_B))),
        )

        for s in [0.0, 0.5, 1.0, 2.0, 5.0, 20.0]:
            rho_s = gksl_flow(rho0, Ls_B, s)
            E_A_num = float(np.real(np.trace(HA @ rho_s)))
            E_A_exact = 4.0 * omega_h * n_FD * (1.0 - n_FD) * (1.0 - math.exp(-0.5 * Gamma * s))
            max_ferm_err = max(max_ferm_err, abs(E_A_num - E_A_exact))

        P0 = np.diag([1.0, 1.0, 0.0, 0.0])
        P1 = np.diag([0.0, 0.0, 1.0, 1.0])
        rho_inf = P0 @ rho0 @ P0 + P1 @ rho0 @ P1
        rho_R = np.array([
            [rho0[0, 0] + rho0[1, 1], rho0[0, 2] + rho0[1, 3]],
            [rho0[2, 0] + rho0[3, 1], rho0[2, 2] + rho0[3, 3]],
        ])
        E_inf_pairs = float(np.real(np.trace(HA @ rho_inf))) / (2.0 * omega_h)
        coh_sq = frob_sq(rho0 - rho_inf)
        S_L_hawking = linear_entropy(rho_R)
        max_ferm_err = max(max_ferm_err, abs(E_inf_pairs - coh_sq), abs(E_inf_pairs - S_L_hawking))
        ferm_curves[str(T_over_w)] = {
            "n_FD": n_FD,
            "gamma_loc": gamma_loc_num,
            "E_A_inf_over_2omega": E_inf_pairs,
            "S_L_hawking": S_L_hawking,
            "dE_A_ds_0": 2.0 * Gamma * omega_h * n_FD * (1.0 - n_FD),
        }

    # (c) Static proportional redshift dephasing example: H_B = 2 H_A (gamma = 0)
    # still damps non-commuting observable <sigma_x> = e^{-Gamma s / 2} on |+><+|
    Hz = 0.5 * sz
    plus = np.array([1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    rho_plus = np.outer(plus, plus.conj())
    rho_red_s2 = gksl_flow(rho_plus, [Hz], 2.0)
    red_vis_s2 = float(np.real(np.trace(sx @ rho_red_s2)))
    red_pur_s2 = float(np.real(np.trace(rho_red_s2 @ rho_red_s2)))
    red_moment_drift = max(
        float(np.linalg.norm(gksl_dual(op, [Hz])))
        for op in [Hz, Hz @ Hz, 2.0 * Hz, 4.0 * (Hz @ Hz)]
    )
    assert red_moment_drift < FLOAT_TOL
    assert abs(red_vis_s2 - math.exp(-1.0)) < FLOAT_TOL
    assert abs(red_pur_s2 - 0.5 * (1.0 + math.exp(-2.0))) < FLOAT_TOL

    # General non-unital GKSL check: expectation conservation L^\dagger(M) = 0 does not
    # imply [M, L_k] = 0 (though second moment L^\dagger(M^2) != 0)
    H_nu = np.diag([0.0, 0.0, 0.0, 1.0]).astype(complex)
    L0_nu = np.zeros((4, 4), dtype=complex); L0_nu[0, 2] = 1.0
    L1_nu = np.zeros((4, 4), dtype=complex); L1_nu[1, 2] = 1.0
    M_nu = np.diag([1.0, -1.0, 0.0, 0.0]).astype(complex)
    nu_bps_res = max(float(np.linalg.norm(gksl_dual(op, [L0_nu, L1_nu]))) for op in [H_nu, H_nu @ H_nu])
    nu_dual_M = float(np.linalg.norm(gksl_dual(M_nu, [L0_nu, L1_nu])))
    nu_comm_norms = [float(np.linalg.norm(comm(M_nu, L))) for L in [L0_nu, L1_nu]]
    nu_dual_M2_diag = np.real(np.diag(gksl_dual(M_nu @ M_nu, [L0_nu, L1_nu]))).tolist()
    assert nu_bps_res < FLOAT_TOL and nu_dual_M < FLOAT_TOL
    assert abs(nu_comm_norms[0] - 1.0) < FLOAT_TOL and abs(nu_comm_norms[1] - 1.0) < FLOAT_TOL
    assert abs(nu_dual_M2_diag[2] - 2.0) < FLOAT_TOL

    # (d) Truncated Bosonic Hawking pair (Fock cutoff N_max = 18)
    Ncut = 18
    b1 = np.zeros((Ncut, Ncut), dtype=complex)
    for n in range(1, Ncut):
        b1[n - 1, n] = math.sqrt(n)
    IN = np.eye(Ncut, dtype=complex)
    bR_b = np.kron(b1, IN)
    bL_b = np.kron(IN, b1)
    NR_b = dag(bR_b) @ bR_b
    NL_b = dag(bL_b) @ bL_b
    HB_b = omega_h * (NR_b - NL_b)

    boson_checks = {}
    max_boson_rel_err = 0.0
    max_boson_comm_HA_HB = 0.0
    for T_over_w in [0.15, 0.25, 0.4, 0.6, 0.8]:
        th = math.exp(-0.5 / T_over_w)
        r = math.atanh(th)
        n_BE = 1.0 / (math.exp(1.0 / T_over_w) - 1.0)
        psi = np.zeros(Ncut * Ncut, dtype=complex)
        for n in range(Ncut):
            psi[n * Ncut + n] = (th ** n) / math.cosh(r)
        psi /= np.linalg.norm(psi)
        HA_b = omega_h * (
            math.cosh(2 * r) * (NR_b + NL_b + np.eye(Ncut * Ncut))
            - math.sinh(2 * r) * (dag(bR_b) @ dag(bL_b) + bR_b @ bL_b)
            - np.eye(Ncut * Ncut)
        )
        max_boson_comm_HA_HB = max(max_boson_comm_HA_HB, float(np.linalg.norm(comm(HA_b, HB_b))))
        Ldag_HA = -0.5 * Gamma * comm(NR_b, comm(NR_b, HA_b))
        rate_num = float(np.real(psi.conj() @ (Ldag_HA @ psi)))
        rate_exact = 2.0 * Gamma * omega_h * n_BE * (1.0 + n_BE)
        rel_err = abs(rate_num - rate_exact) / max(rate_exact, 1e-15)
        max_boson_rel_err = max(max_boson_rel_err, rel_err)
        boson_checks[str(T_over_w)] = {
            "n_BE": n_BE,
            "rate_num": rate_num,
            "rate_exact": rate_exact,
            "rel_err": rel_err,
        }

    return {
        "max_two_level_gamma_error": max_2lvl_err,
        "max_fermionic_HA_HB_commutator": max_ferm_comm_HA_HB,
        "max_fermionic_gamma_loc_error": max_ferm_gamma_loc_err,
        "max_fermionic_exact_error": max_ferm_err,
        "max_fermionic_HB_conservation_error": max_ferm_hb_err,
        "max_bosonic_HA_HB_commutator": max_boson_comm_HA_HB,
        "max_bosonic_trunc_rel_error": max_boson_rel_err,
        "bilocal_vs_local_hawking_pi_over_6": {
            "comm_HA_HB_norm": bilocal_comm_norm,
            "bilocal_HB_jump_BPS_residual": bilocal_bps_res,
            "bilocal_HB_jump_nontrivial_norm_sq": bilocal_nontrivial_sq,
            "exterior_local_gamma_loc": gamma_loc_pi6,
        },
        "proportional_redshift_dephasing_example": {
            "gamma_clock_incompatibility": 0.0,
            "energy_moment_drift": red_moment_drift,
            "sigma_x_visibility_s0": 1.0,
            "sigma_x_visibility_s2": red_vis_s2,
            "exact_exp_minus_1": math.exp(-1.0),
            "purity_s2": red_pur_s2,
        },
        "nonunital_gksl_fixed_point_check": {
            "energy_bps_residual": nu_bps_res,
            "dual_M_norm": nu_dual_M,
            "commutator_M_jump_norms": nu_comm_norms,
            "dual_M_squared_diagonal": nu_dual_M2_diag,
        },
        "fermionic_samples": ferm_curves,
        "bosonic_samples": boson_checks,
    }


# ==============================================================================
# 3. VERIFY THEOREM 3 (Monogamy, Valid Choi Saturation, Kay 2009 & Decoder CPL)
# ==============================================================================
def verify_theorem_3() -> dict:
    results = {}
    for d in [2, 3, 4, 5]:
        dim = d ** 3
        Phi = np.eye(d, dtype=complex).ravel() / math.sqrt(d)
        P_phi = np.outer(Phi, Phi.conj())
        Id = np.eye(d, dtype=complex)

        PA = np.kron(P_phi, Id)
        PB = PA.reshape(d, d, d, d, d, d).transpose(0, 2, 1, 3, 5, 4).reshape(dim, dim)

        alg_err = float(np.linalg.norm(PA @ PB @ PA - (1.0 / (d ** 2)) * PA))
        evals = np.linalg.eigvalsh(PA + PB)
        max_eig = float(np.max(evals))
        bound = 1.0 + 1.0 / d

        # Valid CPTP Choi saturation state sigma_* = (1/d) sum_j |psi_j><psi_j|
        # |psi_j> = (|Phi_d>_{RA'}|j>_{B'} + |Phi_d>_{RB'}|j>_{A'}) / sqrt(2 + 2/d)
        sigma_star = np.zeros((dim, dim), dtype=complex)
        norm_factor = math.sqrt(2.0 + 2.0 / d)
        for j in range(d):
            ej = np.eye(d, dtype=complex)[j]
            u_j = np.kron(Phi, ej)
            v_j = u_j.reshape(d, d, d).transpose(0, 2, 1).ravel()
            psi_j = (u_j + v_j) / norm_factor
            sigma_star += np.outer(psi_j, psi_j.conj()) / d
        marginal_R = np.einsum("rabsab->rs", sigma_star.reshape(d, d, d, d, d, d))
        choi_marg_err = float(np.linalg.norm(marginal_R - Id / d))
        FA_star = float(np.real(np.trace(PA @ sigma_star)))
        FB_star = float(np.real(np.trace(PB @ sigma_star)))
        assert choi_marg_err < FLOAT_TOL
        assert abs(FA_star - 0.5 * bound) < FLOAT_TOL
        assert abs(FB_star - 0.5 * bound) < FLOAT_TOL

        # Comparison product state |Phi_d>_{RA'} x |0>_{B'} attains (1, 1/d^2)
        prod_v = np.kron(Phi, np.eye(d, dtype=complex)[0])
        FA_prod = float(np.real(prod_v.conj() @ (PA @ prod_v)))
        FB_prod = float(np.real(prod_v.conj() @ (PB @ prod_v)))
        assert abs(FA_prod - 1.0) < FLOAT_TOL
        assert abs(FB_prod - 1.0 / (d * d)) < FLOAT_TOL

        # Check 500 random pure states against BOTH linear sum bound AND Kay (2009) curved bound
        max_sum = 0.0
        max_kay_violation = 0.0
        for _ in range(500):
            v = rng.normal(size=dim) + 1j * rng.normal(size=dim)
            v /= np.linalg.norm(v)
            fa = float(np.real(v.conj() @ (PA @ v)))
            fb = float(np.real(v.conj() @ (PB @ v)))
            max_sum = max(max_sum, fa + fb)
            fb_kay = float(kay_curved_bound(fa, d))
            max_kay_violation = max(max_kay_violation, fb - fb_kay)
        assert max_kay_violation < FLOAT_TOL

        results[f"d={d}"] = {
            "P_A_P_B_P_A_error": alg_err,
            "max_eig_PA_plus_PB": max_eig,
            "theoretical_linear_bound": bound,
            "bound_match_error": abs(max_eig - bound),
            "valid_choi_saturation_FA": FA_star,
            "valid_choi_saturation_FB": FB_star,
            "valid_choi_marginal_error": choi_marg_err,
            "product_state_FA": FA_prod,
            "product_state_FB_actual_1_over_d2": FB_prod,
            "random_max_FA_plus_FB": max_sum,
            "random_max_kay_curved_violation": max_kay_violation,
        }

    # Explicit decoder check: V = sigma_z (d=2) has F_e(Ad_V) = 0 without decoder,
    # F_e(Ad_{V^dag} o Ad_V) = 1 with decoder
    sz = np.array([[1, 0], [0, -1]], dtype=complex)
    Fe_no_dec = float(abs(np.trace(sz)) ** 2 / 4.0)
    Fe_with_dec = float(abs(np.trace(dag(sz) @ sz)) ** 2 / 4.0)
    assert abs(Fe_no_dec) < FLOAT_TOL
    assert abs(Fe_with_dec - 1.0) < FLOAT_TOL

    results["kay_2009_reference_point_d2_FA09"] = {
        "d": 2,
        "FA": 0.9,
        "kay_curved_FB_max": float(kay_curved_bound(0.9, 2)),
        "linear_sum_FB_max": 0.6,
    }
    results["decoder_fidelity_check"] = {
        "V_sigma_z_Fe_without_decoder": Fe_no_dec,
        "V_sigma_z_Fe_with_inverse_decoder": Fe_with_dec,
    }
    return results


# ==============================================================================
# 4. VERIFY THEOREMS 4 & 5 + UNIFIED TWO-WINDOW BH MODEL + COMPANION GALERKIN YM
# ==============================================================================
def build_ym_fock_hamiltonian(cutoff: int, g_YM: float = 0.8, m_reg: float = 0.35):
    """Build 6-oscillator bosonic SU(2) 2-matrix Yang-Mills Hamiltonian up to total quanta <= cutoff."""
    basis = [t for t in itertools.product(range(cutoff + 1), repeat=6) if sum(t) <= cutoff]
    idx_map = {st: i for i, st in enumerate(basis)}
    D = len(basis)
    ads = []
    for mode in range(6):
        rows, cols, vals = [], [], []
        for st, j in idx_map.items():
            if sum(st) < cutoff:
                lst = list(st)
                lst[mode] += 1
                rows.append(idx_map[tuple(lst)])
                cols.append(j)
                vals.append(math.sqrt(lst[mode]))
        ads.append(sp.csc_matrix((vals, (rows, cols)), shape=(D, D), dtype=complex))
    a = [ad.getH() for ad in ads]
    X = [(aa + ad) / math.sqrt(2.0) for aa, ad in zip(a, ads)]
    P = [1j * (ad - aa) / math.sqrt(2.0) for aa, ad in zip(a, ads)]
    eps = [(0, 1, 2, 1), (0, 2, 1, -1), (1, 2, 0, 1), (1, 0, 2, -1), (2, 0, 1, 1), (2, 1, 0, -1)]

    J_exact = [sp.csc_matrix((D, D), dtype=complex) for _ in range(3)]
    for aa, bb, cc, sgn in eps:
        J_exact[aa] += -1j * sgn * (ads[bb] @ a[cc] + ads[3 + bb] @ a[3 + cc])

    V_comm = sp.csc_matrix((D, D), dtype=complex)
    for aa in range(3):
        C_a = sum(sgn * (X[bb] @ X[3 + cc]) for aa2, bb, cc, sgn in eps if aa2 == aa)
        V_comm += C_a @ C_a

    H = (
        0.5 * sum(pp @ pp for pp in P)
        + 0.5 * (g_YM ** 2) * V_comm
        + 0.5 * (m_reg ** 2) * sum(xx @ xx for xx in X)
    )
    return basis, idx_map, H, J_exact


def petz_entanglement_fidelity(rho_ref_out: np.ndarray, d_ref: int = 2) -> float:
    """Exact entanglement fidelity F_e(R_Petz o N) = (1/d_ref) Tr[((I x sigma^{-1/4}) rho (I x sigma^{-1/4}))^2]."""
    d_out = rho_ref_out.shape[0] // d_ref
    rho_4 = rho_ref_out.reshape(d_ref, d_out, d_ref, d_out)
    sigma = np.einsum("aibj,ab->ij", rho_4, np.eye(d_ref))
    evals, evecs = np.linalg.eigh(0.5 * (sigma + dag(sigma)))
    safe_evals = np.where(evals > 1e-12, evals, 1.0)
    inv_q = np.where(evals > 1e-12, safe_evals ** (-0.25), 0.0)
    sig_m14 = evecs @ np.diag(inv_q) @ dag(evecs)
    op = np.kron(np.eye(d_ref), sig_m14)
    M = op @ rho_ref_out @ op
    return float(np.real(np.trace(M @ M)) / d_ref)


def verify_matrix_bh_and_theorems_4_5() -> dict:
    # --- Part A: Theorem 5 Bottleneck Bound (k_enc = max(2, ceil(dC / df))) ---
    bottleneck_checks = {}
    for dC, df in [(4, 1), (4, 2), (4, 3), (6, 2), (6, 3)]:
        bound = min(1.0, (df / dC) ** 2)
        k_enc = max(2, math.ceil(dC / df))
        k_dec = max(2, math.ceil(df / dC))
        max_rand_Fe = 0.0
        max_tp_err_E = 0.0
        max_tp_err_R = 0.0
        for _ in range(300):
            M1 = rng.normal(size=(k_enc * df, dC)) + 1j * rng.normal(size=(k_enc * df, dC))
            Q1, _ = np.linalg.qr(M1)
            assert Q1.shape == (k_enc * df, dC), f"Unexpected Q1 shape {Q1.shape}"
            Es = [Q1[i * df:(i + 1) * df, :] for i in range(k_enc)]
            tp_E = sum(dag(E) @ E for E in Es)
            assert tp_E.shape == (dC, dC)
            tp_err_E = float(np.linalg.norm(tp_E - np.eye(dC)))
            assert tp_err_E < FLOAT_TOL
            max_tp_err_E = max(max_tp_err_E, tp_err_E)

            M2 = rng.normal(size=(k_dec * dC, df)) + 1j * rng.normal(size=(k_dec * dC, df))
            Q2, _ = np.linalg.qr(M2)
            assert Q2.shape == (k_dec * dC, df), f"Unexpected Q2 shape {Q2.shape}"
            Rs = [Q2[i * dC:(i + 1) * dC, :] for i in range(k_dec)]
            tp_R = sum(dag(R) @ R for R in Rs)
            assert tp_R.shape == (df, df)
            tp_err_R = float(np.linalg.norm(tp_R - np.eye(df)))
            assert tp_err_R < FLOAT_TOL
            max_tp_err_R = max(max_tp_err_R, tp_err_R)

            Fe = sum(abs(np.trace(R @ E)) ** 2 for E in Es for R in Rs) / (dC ** 2)
            assert Fe <= bound + FLOAT_TOL
            max_rand_Fe = max(max_rand_Fe, float(Fe))

        # Exact saturating CPTP channel (projection + complement reset)
        E0 = np.zeros((df, dC), dtype=complex)
        for i in range(df):
            E0[i, i] = 1.0
        Es_opt = [E0]
        for j in range(df, dC):
            Ej = np.zeros((df, dC), dtype=complex)
            Ej[0, j] = 1.0
            Es_opt.append(Ej)
        assert float(np.linalg.norm(sum(dag(E) @ E for E in Es_opt) - np.eye(dC))) < FLOAT_TOL
        R0 = dag(E0)
        assert float(np.linalg.norm(dag(R0) @ R0 - np.eye(df))) < FLOAT_TOL
        Fe_opt = sum(abs(np.trace(R0 @ E)) ** 2 for E in Es_opt) / (dC ** 2)
        assert abs(Fe_opt - bound) < FLOAT_TOL

        bottleneck_checks[f"dC={dC},df={df}"] = {
            "dC": dC,
            "df": df,
            "encoder_kraus_count": k_enc,
            "decoder_kraus_count": k_dec,
            "trials": 300,
            "max_TP_residual_E": max_tp_err_E,
            "max_TP_residual_R": max_tp_err_R,
            "theoretical_bound": bound,
            "max_random_Fe": max_rand_Fe,
            "saturating_Fe": float(Fe_opt),
            "saturation_error": abs(float(Fe_opt) - bound),
        }

    # Independent Petz Choi-formula vs explicit Kraus-operator cross-check (100 random trials)
    max_petz_kraus_diff = 0.0
    for dc, dout, k_cr in [(2, 1, 2), (2, 2, 3), (2, 4, 2), (3, 2, 3), (3, 5, 2)]:
        for _ in range(20):
            X = rng.normal(size=(dout * k_cr, dc)) + 1j * rng.normal(size=(dout * k_cr, dc))
            Q, _ = np.linalg.qr(X)
            Es = [Q[j * dout:(j + 1) * dout, :] for j in range(k_cr)]
            sig = sum(E @ dag(E) for E in Es) / dc
            vals, vecs = np.linalg.eigh(0.5 * (sig + dag(sig)))
            mask = vals > 1e-12
            sinvh = (vecs[:, mask] * (vals[mask] ** (-0.5))) @ dag(vecs[:, mask])
            Rs = [dag(E) @ sinvh / math.sqrt(dc) for E in Es]
            Fe_kraus = float(sum(abs(np.trace(R @ E)) ** 2 for E in Es for R in Rs) / (dc ** 2))
            J = sum(np.outer(E.T.reshape(-1), E.T.reshape(-1).conj()) for E in Es) / dc
            Fe_choi = petz_entanglement_fidelity(J, d_ref=dc)
            max_petz_kraus_diff = max(max_petz_kraus_diff, abs(Fe_kraus - Fe_choi))
    assert max_petz_kraus_diff < FLOAT_TOL

    # --- Part B: Independent Companion SU(2) YM 2-Matrix Model (True Galerkin Projection) ---
    b3, ix3, H3_naive, Jex3 = build_ym_fock_hamiltonian(cutoff=3)
    b5, ix5, H5, _ = build_ym_fock_hamiltonian(cutoff=5)
    b6, ix6, H6, _ = build_ym_fock_hamiltonian(cutoff=6)
    sel5 = [ix5[st] for st in b3]
    sel6 = [ix6[st] for st in b3]
    H_galerkin_5 = H5[sel5, :][:, sel5].toarray()
    H_galerkin_6 = H6[sel6, :][:, sel6].toarray()
    galerkin_5_vs_6_diff = float(np.linalg.norm(H_galerkin_5 - H_galerkin_6))
    assert galerkin_5_vs_6_diff < FLOAT_TOL

    J2_exact = sum((j @ j) for j in Jex3).toarray()
    evals_J2, evecs_J2 = np.linalg.eigh(0.5 * (J2_exact + dag(J2_exact)))
    U_sing = evecs_J2[:, np.abs(evals_J2) < 1e-9]
    d_sing = int(U_sing.shape[1])
    H_YM_sing_galerkin = dag(U_sing) @ H_galerkin_5 @ U_sing
    H_YM_sing_galerkin = 0.5 * (H_YM_sing_galerkin + dag(H_YM_sing_galerkin))
    ym_galerkin_evals = np.linalg.eigvalsh(H_YM_sing_galerkin)

    H_YM_sing_naive = dag(U_sing) @ H3_naive.toarray() @ U_sing
    H_YM_sing_naive = 0.5 * (H_YM_sing_naive + dag(H_YM_sing_naive))
    ym_naive_evals = np.linalg.eigvalsh(H_YM_sing_naive)
    naive_vs_galerkin_singlet_matrix_diff = float(np.linalg.norm(H_YM_sing_naive - H_YM_sing_galerkin))
    naive_vs_galerkin_eval_l2_diff = float(np.linalg.norm(ym_galerkin_evals - ym_naive_evals))

    # --- Part C: Unified Finite-Width Two-Window N=8-Qubit Evaporating BH Model ---
    # Piecewise time-dependent driving on H_tot = H_win1 (+) H_win2 (dim = 256 + 4 = 260):
    #   * Reference window Hamiltonian H_tot = H_win1 (+) H_win2 defines the two energy windows
    #     Window 1 ([E1 - Delta, E1 + Delta] = [0.8, 1.2]) and Window 2 ([2.8, 3.2]).
    #   * Coarse-grained spectral jump K_B = E1 Pi_1 + E2 Pi_2 commutes with H_dyn(t) on every
    #     piecewise step k = 1..8 ([K_B, H_dyn_k] = 0), guaranteeing exact time-ordered
    #     (t, s) commutation U(t, t0) Phi_B(s) = Phi_B(s) U(t, t0) and exact s-invariance
    #     L_B(rho_true(k)) = 0 across the entire k = 0..8 Page curve.
    n_bh_init = 8
    d1 = 2 ** n_bh_init  # 256
    d2 = 4
    E1, E2, Delta = 1.0, 3.0, 0.2

    G1 = rng.normal(size=(d1, d1)) + 1j * rng.normal(size=(d1, d1))
    H_raw1 = 0.5 * (G1 + dag(G1))
    e1_min, e1_max = float(np.min(np.linalg.eigvalsh(H_raw1))), float(np.max(np.linalg.eigvalsh(H_raw1)))
    H_win1 = E1 * np.eye(d1, dtype=complex) + Delta * (
        2.0 * (H_raw1 - e1_min * np.eye(d1)) / (e1_max - e1_min) - np.eye(d1)
    )
    e1_check = np.linalg.eigvalsh(H_win1)
    assert e1_check[0] >= E1 - Delta - 1e-12 and e1_check[-1] <= E1 + Delta + 1e-12

    G2 = rng.normal(size=(d2, d2)) + 1j * rng.normal(size=(d2, d2))
    H_raw2 = 0.5 * (G2 + dag(G2))
    e2_min, e2_max = float(np.min(np.linalg.eigvalsh(H_raw2))), float(np.max(np.linalg.eigvalsh(H_raw2)))
    H_win2 = E2 * np.eye(d2, dtype=complex) + Delta * (
        2.0 * (H_raw2 - e2_min * np.eye(d2)) / (e2_max - e2_min) - np.eye(d2)
    )

    d_full = d1 + d2
    H_tot = np.zeros((d_full, d_full), dtype=complex)
    H_tot[:d1, :d1] = H_win1
    H_tot[d1:, d1:] = H_win2
    Pi1_full = np.diag([1.0] * d1 + [0.0] * d2).astype(complex)
    Pi2_full = np.diag([0.0] * d1 + [1.0] * d2).astype(complex)
    KB_full = E1 * Pi1_full + E2 * Pi2_full

    comm_KB_Htot = float(np.linalg.norm(comm(KB_full, H_tot)))
    assert comm_KB_Htot < FLOAT_TOL

    # Initial state on R_ref (d_C = 2) x Window 1 (d1 = 256):
    # Young BH carrying one qubit maximally entangled with external reference R_ref
    # (joint BH+R_ref state initially pure; reduced 256D Window-1 state has rank 2, purity 1/2)
    psi = np.zeros((2, d1), dtype=complex)
    psi[0, 0] = 1.0 / math.sqrt(2.0)
    psi[1, 1] = 1.0 / math.sqrt(2.0)

    # Exact partial trace over reference R_ref yielding the 256D Window-1 state
    # rho_win1(0)[a, b] = sum_r psi[r, a] * conj(psi[r, b])
    rho_bh_0 = psi.T @ psi.conj()
    rho_bh_0_check = np.einsum("ra,rb->ab", psi, psi.conj())
    assert np.allclose(rho_bh_0, rho_bh_0_check, atol=FLOAT_TOL, rtol=0)
    intra_window_t_comm_norm = float(np.linalg.norm(comm(H_win1, rho_bh_0)))
    assert intra_window_t_comm_norm > 0.05

    tau_scr = 25.0
    U_win1_step = expm(-1j * tau_scr * H_win1)

    k_vals = list(range(n_bh_init + 1))
    S_rad_list = []
    S_L_rad_list = []
    F_rad_petz = []
    F_bh_petz = []
    F_bottleneck_bh = []
    H_win1_exp_list = []
    U_step_comm_H_win1_list = []
    max_window1_s_dissipation = 0.0
    max_KB_Hdyn_comm = 0.0

    psi_curr = psi.copy()
    for k in k_vals:
        if k == 0:
            U_step_win1 = np.eye(d1, dtype=complex)
            H_dyn_win1 = H_win1
        elif k == 1:
            psi_curr = psi_curr @ U_win1_step.T
            U_step_win1 = U_win1_step
            H_dyn_win1 = H_win1
        else:
            n_rem_prev = n_bh_init - k + 1
            d_rem_prev = 2 ** n_rem_prev
            d_rad_prev = 2 ** (k - 1)
            G_loc = rng.normal(size=(d_rem_prev, d_rem_prev)) + 1j * rng.normal(size=(d_rem_prev, d_rem_prev))
            H_loc = 0.5 * (G_loc + dag(G_loc)) / math.sqrt(d_rem_prev)
            U_loc = expm(-1j * 2.0 * H_loc)
            psi_3 = psi_curr.reshape(2, d_rem_prev, d_rad_prev)
            psi_curr = np.einsum("ab,rbc->rac", U_loc, psi_3).reshape(2, d1)
            U_step_win1 = np.kron(U_loc, np.eye(d_rad_prev, dtype=complex))
            H_dyn_win1 = np.kron(H_loc, np.eye(d_rad_prev, dtype=complex))

        # Verify piecewise H_dyn(t) commutes with K_B on the full two-window space,
        # so the induced unitary channel U(t,t_0) = Ad_{U(t,t_0)} commutes with Phi_B(s)
        H_dyn_full = np.zeros((d_full, d_full), dtype=complex)
        H_dyn_full[:d1, :d1] = H_dyn_win1
        H_dyn_full[d1:, d1:] = H_win2
        comm_kb_dyn = float(np.linalg.norm(comm(KB_full, H_dyn_full)))
        assert comm_kb_dyn < FLOAT_TOL
        max_KB_Hdyn_comm = max(max_KB_Hdyn_comm, comm_kb_dyn)

        # Exact partial trace over R_ref yielding the 256D Window-1 state rho_win1(k)
        # (remaining BH + emitted radiation for k > 0), cross-checked against einsum
        rho_bh_k = psi_curr.T @ psi_curr.conj()
        rho_bh_k_check = np.einsum("ra,rb->ab", psi_curr, psi_curr.conj())
        assert np.allclose(rho_bh_k, rho_bh_k_check, atol=FLOAT_TOL, rtol=0)
        H_win1_exp_list.append(float(np.real(np.trace(H_win1 @ rho_bh_k))))
        U_step_comm_H_win1_list.append(float(np.linalg.norm(comm(U_step_win1, H_win1))))

        rho_bh_k_full = np.zeros((d_full, d_full), dtype=complex)
        rho_bh_k_full[:d1, :d1] = rho_bh_k
        s_diss_k = float(np.linalg.norm(gksl(rho_bh_k_full, [KB_full])))
        assert s_diss_k < FLOAT_TOL
        max_window1_s_dissipation = max(max_window1_s_dissipation, s_diss_k)

        d_rem = 2 ** (n_bh_init - k)
        d_rad = 2 ** k
        psi_3 = psi_curr.reshape(2, d_rem, d_rad)

        rho_rad = np.einsum("rba,rbc->ac", psi_3, psi_3.conj())
        S_rad_list.append(vn_entropy(rho_rad))
        S_L_rad_list.append(linear_entropy(rho_rad))

        rho_ref_rad = np.einsum("rba,sbd->rasd", psi_3, psi_3.conj()).reshape(2 * d_rad, 2 * d_rad)
        F_rad_petz.append(petz_entanglement_fidelity(rho_ref_rad, d_ref=2))

        rho_ref_bh = np.einsum("rba,sda->rbsd", psi_3, psi_3.conj()).reshape(2 * d_rem, 2 * d_rem)
        F_bh_petz.append(petz_entanglement_fidelity(rho_ref_bh, d_ref=2))
        F_bottleneck_bh.append(min(1.0, (d_rem / 2.0) ** 2))

    # --- Part D: Double-Uncertainty, Inter-Window s-Flow Limit & Unrelated-Pinching Check ---
    # Use a 4+4=8D slice spanning Window 1 (4 basis states) and Window 2 (4 basis states)
    # so exact expm(s L_B) can be verified alongside Theorem 4 identities.
    d_shell = 4
    w1, w2 = 0.6, 0.4
    v1 = rng.normal(size=d_shell) + 1j * rng.normal(size=d_shell)
    v1 /= np.linalg.norm(v1)
    v1b = rng.normal(size=d_shell) + 1j * rng.normal(size=d_shell)
    v1b /= np.linalg.norm(v1b)
    v2 = rng.normal(size=d_shell) + 1j * rng.normal(size=d_shell)
    v2 /= np.linalg.norm(v2)
    psi_a = np.concatenate([math.sqrt(w1) * v1, math.sqrt(w2) * v2])
    psi_b = np.concatenate([math.sqrt(w1) * v1b, math.sqrt(w2) * v2])
    rho_double = 0.7 * np.outer(psi_a, psi_a.conj()) + 0.3 * np.outer(psi_b, psi_b.conj())
    Pi1 = np.diag([1.0] * d_shell + [0.0] * d_shell).astype(complex)
    Pi2 = np.diag([0.0] * d_shell + [1.0] * d_shell).astype(complex)
    KB = E1 * Pi1 + E2 * Pi2
    rho_pinched = Pi1 @ rho_double @ Pi1 + Pi2 @ rho_double @ Pi2

    # Verify exact spectral block-decay: e^{s L_B}(rho) = P(rho) + e^{-(E1-E2)^2 s / 2}(rho - P(rho))
    max_block_decay_err = 0.0
    for s_val in [0.0, 0.25, 1.0, 3.0, 10.0]:
        rho_s = gksl_flow(rho_double, [KB], s_val)
        rho_exact = rho_pinched + math.exp(-0.5 * ((E1 - E2) ** 2) * s_val) * (rho_double - rho_pinched)
        max_block_decay_err = max(max_block_decay_err, float(np.linalg.norm(rho_s - rho_exact)))
    assert max_block_decay_err < FLOAT_TOL

    pyth_lhs = linear_entropy(rho_pinched)
    pyth_rhs = linear_entropy(rho_double) + frob_sq(rho_double - rho_pinched)
    pyth_err = abs(pyth_lhs - pyth_rhs)
    vn_lhs = vn_entropy(rho_pinched)
    vals_p, vecs_p = np.linalg.eigh(rho_pinched)
    log_p = vecs_p @ np.diag(np.where(vals_p > 1e-14, np.log(np.maximum(vals_p, 1e-14)), 0.0)) @ dag(vecs_p)
    D_rel = float(-vn_entropy(rho_double) - np.real(np.trace(rho_double @ log_p)))
    vn_decomp_err = abs(vn_lhs - (vn_entropy(rho_double) + D_rel))

    L_rho = gksl(rho_double, [KB])
    pw_lhs = float(2.0 * np.real(np.trace(rho_double @ L_rho)))
    pw_rhs = -frob_sq(comm(KB, rho_double))
    pw_err = abs(pw_lhs - pw_rhs)

    rho_micro = Pi1 @ rho_double @ Pi1
    rho_micro /= np.trace(rho_micro)
    micro_err = float(np.linalg.norm(gksl(rho_micro, [KB])))

    # Unrelated-pinching example: K = sigma_x, rho = |+><+|, P = sigma_z pinching
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    plus = np.array([1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    rho_plus = np.outer(plus, plus.conj())
    Pz_rho = np.diag(np.diag(rho_plus))
    unrelated_flow_diff = float(np.linalg.norm(gksl_flow(rho_plus, [sx], 10.0) - rho_plus))
    unrelated_pinch_coh_sq = frob_sq(rho_plus - Pz_rho)
    assert unrelated_flow_diff < FLOAT_TOL
    assert abs(unrelated_pinch_coh_sq - 0.5) < FLOAT_TOL

    return {
        "bottleneck_checks": bottleneck_checks,
        "dC4_df2_fidelity_vs_prob_distinction": {
            "max_entanglement_fidelity": 0.25,
            "complete_erasure_entanglement_fidelity": 0.0625,
            "uniform_subspace_projection_probability": 0.5,
        },
        "petz_formula_vs_explicit_kraus_max_diff": max_petz_kraus_diff,
        "su2_ym_companion_galerkin": {
            "note": "Independent companion 2-matrix SU(2) YM spectrum benchmark (decoupled from N=8 Page curve).",
            "g_YM": 0.8,
            "m_reg": 0.35,
            "fock_cutoff": 3,
            "fock_dim": len(b3),
            "intermediate_polynomial_cutoff": 5,
            "galerkin_cutoff_5_vs_6_diff": galerkin_5_vs_6_diff,
            "exact_singlet_dim": d_sing,
            "galerkin_singlet_energies": [float(x) for x in ym_galerkin_evals],
            "naive_pretruncated_singlet_energies": [float(x) for x in ym_naive_evals],
            "naive_vs_galerkin_singlet_matrix_frob_diff": naive_vs_galerkin_singlet_matrix_diff,
            "naive_vs_galerkin_eigenvalue_vec_l2_diff": naive_vs_galerkin_eval_l2_diff,
        },
        "unified_two_window_evaporation": {
            "E1": E1,
            "E2": E2,
            "Delta": Delta,
            "window1_dim": d1,
            "window2_dim": d2,
            "comm_KB_Htot_norm": comm_KB_Htot,
            "max_comm_KB_Hdyn_norm": max_KB_Hdyn_comm,
            "intra_window_t_comm_norm": intra_window_t_comm_norm,
            "max_window1_s_dissipation_over_page_curve": max_window1_s_dissipation,
            "reference_H_win1_expectation_per_step": H_win1_exp_list,
            "step_U_comm_H_win1_norm": U_step_comm_H_win1_list,
            "k_emitted": k_vals,
            "S_rad_vn_nats": S_rad_list,
            "S_rad_vn_bits": [x / math.log(2.0) for x in S_rad_list],
            "S_rad_linear": S_L_rad_list,
            "F_rad_petz": F_rad_petz,
            "F_bh_petz": F_bh_petz,
            "F_sum_bh_plus_rad": [a + b for a, b in zip(F_bh_petz, F_rad_petz)],
            "F_bottleneck_bh_bound": F_bottleneck_bh,
            "max_F_sum": max(a + b for a, b in zip(F_bh_petz, F_rad_petz)),
        },
        "double_uncertainty": {
            "S_L_initial_layer1": linear_entropy(rho_double),
            "coherence_sq_layer2": frob_sq(rho_double - rho_pinched),
            "S_L_pinched_total": pyth_lhs,
            "pythagorean_error": pyth_err,
            "vn_decomposition_error": vn_decomp_err,
            "parisi_wu_monotonicity_error": pw_err,
            "microcanonical_invariance_error": micro_err,
            "max_spectral_block_decay_error": max_block_decay_err,
            "unrelated_pinching_example": {
                "actual_flow_change_s10": unrelated_flow_diff,
                "unrelated_pinch_coh_sq": unrelated_pinch_coh_sq,
            },
        },
    }


# ==============================================================================
# 5. GENERATE PUBLICATION-QUALITY FIGURES (PDF)
# ==============================================================================
def make_figures(res2: dict, res45: dict) -> None:
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 10,
        "axes.labelsize": 10.5,
        "axes.titlesize": 10.5,
        "legend.fontsize": 8.4,
        "xtick.labelsize": 9.2,
        "ytick.labelsize": 9.2,
        "figure.dpi": 300,
    })

    # --- Figure 1: Exact Horizon Mode Excitation vs Hawking Temperature ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.7))
    T_grid = np.linspace(0.05, 2.5, 300)
    n_FD = 1.0 / (np.exp(1.0 / T_grid) + 1.0)
    n_BE = 1.0 / (np.exp(1.0 / T_grid) - 1.0)
    rate_FD = 2.0 * n_FD * (1.0 - n_FD)
    rate_BE = 2.0 * n_BE * (1.0 + n_BE)

    ax1.semilogy(T_grid, rate_BE, color="#1f4e79", lw=2.0, label=r"Bosons: $2\,n_{\mathrm{BE}}(1+n_{\mathrm{BE}})$")
    ax1.semilogy(T_grid, rate_FD, color="#c0392b", lw=2.0, ls="--", label=r"Fermions: $2\,n_{\mathrm{FD}}(1-n_{\mathrm{FD}})$")
    Tb = [float(k) for k in res2["bosonic_samples"]]
    rb = [res2["bosonic_samples"][k]["rate_num"] for k in res2["bosonic_samples"]]
    Tf = [float(k) for k in res2["fermionic_samples"] if float(k) <= 2.5]
    rf = [res2["fermionic_samples"][k]["dE_A_ds_0"] for k in res2["fermionic_samples"] if float(k) <= 2.5]
    ax1.scatter(Tb, rb, color="#1f4e79", s=26, zorder=5, label=r"Boson Fock check ($N_{\mathrm{cut}}=18$)")
    ax1.scatter(Tf, rf, color="#c0392b", marker="s", s=24, zorder=5, label="Fermion 4D exact check")
    ax1.set_xlabel(r"Hawking temperature $T_H / \omega$")
    ax1.set_ylabel(r"Initial excitation rate $(\Gamma\omega)^{-1}\partial_s\langle H_A\rangle|_{s=0}$")
    ax1.set_title(r"(a) Exterior-local $\mathcal{L}_B$ excites $|0_A\rangle$ ($T_H>0, \Gamma>0$)")
    ax1.set_ylim(1e-5, 3e1)
    ax1.grid(True, which="both", alpha=0.25)
    ax1.legend(loc="lower right", frameon=True, framealpha=0.93)

    s_grid = np.linspace(0.0, 10.0, 200)
    for T_val, col, ls in [(0.25, "#7f8c8d", ":"), (0.5, "#2980b9", "-."), (1.0, "#1f4e79", "-"), (2.0, "#c0392b", "--")]:
        nf = 1.0 / (math.exp(1.0 / T_val) + 1.0)
        SL = 2.0 * nf * (1.0 - nf)
        ax2.plot(s_grid, SL * (1.0 - np.exp(-0.5 * s_grid)), color=col, lw=1.9, ls=ls,
                 label=rf"$T_H/\omega={T_val:g}$ ($S_L={SL:.3f}$)")
    ax2.set_xlabel(r"Dimensionless actualization parameter $\Gamma s$ ($\Gamma>0$)")
    ax2.set_ylabel(r"Excited pair number $\langle H_A\rangle_{\rho_B(s)} / (2\omega)$")
    ax2.set_title(r"(b) Saturation $\langle H_A\rangle_{\rho_B(\infty)}/(2\omega) = S_L(\rho_R^{\mathrm{Hawking}})$")
    ax2.set_ylim(-0.02, 0.56)
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="lower right", frameon=True, framealpha=0.93)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_horizon_heating.pdf")
    plt.close(fig)

    # --- Figure 2: Kay (2009) Curved Boundary + Linear Sum Envelope & Bottleneck ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.7))
    fa = np.linspace(0.0, 1.0, 400)
    # Plot Kay et al. (2009) curved achievable boundary & linear tangent sum outer envelope
    for dC, col, ls in [(2, "#1f4e79", "-"), (3, "#2e7d32", "-."), (8, "#8e44ad", ":")]:
        fb_kay = kay_curved_bound(fa, dC)
        ax1.plot(fa, fb_kay, color=col, lw=2.0, ls=ls,
                 label=rf"Kay (2009) curved bound ($d_C={dC}$)")
        # Symmetric Choi saturation tangent point ((1+1/d)/2, (1+1/d)/2)
        sym_pt = 0.5 * (1.0 + 1.0 / dC)
        ax1.scatter([sym_pt], [sym_pt], color=col, s=34, zorder=6)
    # Linear sum outer envelope for d_C = 2 (tangent to curved bound at (0.75, 0.75))
    fb_lin2 = np.minimum(1.0, 1.5 - fa)
    ax1.plot(fa, fb_lin2, color="#1f4e79", lw=1.4, ls="--", alpha=0.85,
             label=r"Thm. 3 linear sum envelope ($d_C=2$: $F_A+F_B\leq 1.5$)")
    ax1.fill_between(fa, 0, kay_curved_bound(fa, 2), color="#1f4e79", alpha=0.09)
    ax1.scatter([0.75], [0.75], color="#1f4e79", s=34, zorder=6, label=r"Valid Choi saturation $\sigma_*$")
    ax1.scatter([1.0], [1.0], color="#c0392b", s=85, marker="*", zorder=7,
                label="Separated reversible + CPL")
    ax1.annotate("Forbidden for any\njoint CPTP extension",
                 xy=(0.86, 0.74), xytext=(0.66, 1.04),
                 fontsize=7.8, ha="center", va="center", color="#922b21",
                 bbox=dict(boxstyle="round,pad=0.22", fc="white", ec="#c0392b", alpha=0.94, lw=0.7),
                 arrowprops=dict(arrowstyle="->", color="#922b21", lw=0.95))
    ax1.set_xlabel(r"Infalling recovery fidelity $F_A$")
    ax1.set_ylabel(r"Exterior recovery fidelity $F_B$")
    ax1.set_title(r"(a) Theorem 3: Curved tradeoff, linear sum & separation")
    ax1.set_xlim(0.0, 1.06)
    ax1.set_ylim(0.0, 1.15)
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="lower left", frameon=True, framealpha=0.93, fontsize=7.4)

    # Panel (b): Corrected Theorem 5 bottleneck ceiling
    dS = np.linspace(-0.6, 2.5, 250)
    ceil_curve = np.minimum(1.0, np.exp(-2.0 * dS))
    ax2.plot(dS, ceil_curve, color="#1f4e79", lw=2.2, label=r"Theorem 5 ceiling $\min(1, d_f^2/d_C^2)$")
    ax2.fill_between(dS, 0, ceil_curve, color="#1f4e79", alpha=0.10)
    pts_x, pts_y_opt, pts_y_rnd = [], [], []
    for vals in res45["bottleneck_checks"].values():
        pts_x.append(math.log(vals["dC"] / vals["df"]))
        pts_y_opt.append(vals["saturating_Fe"])
        pts_y_rnd.append(vals["max_random_Fe"])
    ax2.scatter(pts_x, pts_y_opt, color="#c0392b", marker="o", s=36, zorder=5, label="Exact saturating CPTP channels")
    ax2.scatter(pts_x, pts_y_rnd, color="#2e7d32", marker="^", s=34, zorder=5, label=r"Max over 300 valid CPTP trials ($k_{\mathrm{enc}}\geq \lceil d_C/d_f\rceil$)")
    ax2.axvline(0.0, color="#7f8c8d", ls="--", lw=1.0)
    ax2.set_xlabel(r"Dimension deficit $\ln(d_C / d_f)$ (nats)")
    ax2.set_ylabel(r"Entanglement fidelity $F_e(\mathcal{R}\circ\mathcal{E})$")
    ax2.set_title(r"(b) Theorem 5: Intermediate-dimension bottleneck")
    ax2.set_xlim(-0.5, 2.3)
    ax2.set_ylim(-0.03, 1.08)
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.93, fontsize=7.4)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_joint_vs_separated.pdf")
    plt.close(fig)

    # --- Figure 3: Unified Two-Window N=8-Qubit Evaporation Page Curve & Petz Recovery ---
    pc = res45["unified_two_window_evaporation"]
    k = np.array(pc["k_emitted"])
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.7))

    ax1.plot(k, pc["S_rad_vn_bits"], "o-", color="#1f4e79", lw=2.0,
             label=r"Radiation entropy $S(R)/\ln 2$ (Window 1)")
    ax1.plot(k, np.minimum(k, 8 - k + 1), "--", color="#7f8c8d", lw=1.2,
             label=r"Envelope $\min(k, N-k+1)$ (with $R_{\mathrm{ref}}$)")
    ax1.axvline(4.0, color="#c0392b", ls=":", lw=1.2, label="Half-evaporation ($k = N/2$)")
    ax1.set_xlabel(r"Emitted radiation qubits $k$")
    ax1.set_ylabel(r"Entanglement entropy (bits)")
    ax1.set_title(r"(a) Finite-width window $t$-scrambling ($N=8$, young BH)")
    ax1.set_xticks(k)
    ax1.set_ylim(-0.15, 4.35)
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="lower center", frameon=True, framealpha=0.94, fontsize=7.9)

    ax2.plot(k, pc["F_rad_petz"], "o-", color="#1f4e79", lw=2.0, label=r"Exterior radiation Petz $F_B(R)$")
    ax2.plot(k, pc["F_bh_petz"], "s--", color="#c0392b", lw=2.0, label=r"Remaining BH Petz $F_{\mathrm{rem}}$")
    ax2.plot(k, pc["F_sum_bh_plus_rad"], "^:", color="#2e7d32", lw=1.8, label=r"Joint sum $F_{\mathrm{rem}} + F_B(R)$")
    ax2.step(k, pc["F_bottleneck_bh_bound"], where="mid", color="#d35400", ls="--", lw=1.3,
             label=r"Thm. 5 bound on $F_{\mathrm{rem}}$ (binds at $k=8$)")
    ax2.axhline(1.5, color="#8e44ad", ls="-.", lw=1.3, label=r"Thm. 3 linear bound $1 + 1/d_C = 1.5$")
    ax2.set_xlabel(r"Emitted radiation qubits $k$")
    ax2.set_ylabel(r"Entanglement fidelity")
    ax2.set_title(r"(b) Petz recovery & Theorem 3/5 ceilings ($d_C=2$)")
    ax2.set_xticks(k)
    ax2.set_ylim(0.15, 2.08)
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=7.3, ncol=1)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_matrix_evaporation.pdf")
    plt.close(fig)


def main() -> None:
    res1 = verify_theorem_1()
    res2 = verify_theorem_2()
    res3 = verify_theorem_3()
    res45 = verify_matrix_bh_and_theorems_4_5()
    make_figures(res2, res45)

    summary = {
        "metadata": {
            "framework": "OSTQD",
            "date": "2026-11-26",
            "seed": SEED,
            "float_tolerance": FLOAT_TOL,
            "python_version": platform.python_version(),
            "numpy_version": np.__version__,
            "scipy_version": scipy.__version__,
            "matplotlib_version": matplotlib.__version__,
        },
        "theorem_1": res1,
        "theorem_2": res2,
        "theorem_3": res3,
        "theorems_4_5_and_models": res45,
    }
    out_path = DATA_DIR / "numerical_verification.json"
    out_path.write_text(json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")

    print("=== OSTQD NUMERICAL VERIFICATION SUMMARY ===")
    print("Env:", f"Python {platform.python_version()}, NumPy {np.__version__}, SciPy {scipy.__version__}, Matplotlib {matplotlib.__version__}")
    print("Thm 1 carre du champ err:    ", res1["max_carre_du_champ_error"])
    print("Thm 1 var decomp err:        ", res1["max_variance_decomposition_error"])
    print("Thm 1 eigenbasis avg err:    ", res1["max_eigenbasis_avg_variance_error"])
    print("Thm 1 rho_mm drift check:    ", res1["variance_drift_cancellation_rho_mm"])
    print("Thm 1 nonzero-D zero-cov:    ", res1["nonzero_D_zero_covariance_example"])
    print("Thm 1 noncomm PDE norm:      ", res1["noncommuting_pde_example"]["L_adH_minus_adH_L_frob_norm"])
    print("Thm 2 2-level gamma err:     ", res2["max_two_level_gamma_error"])
    print("Thm 2 ferm [HA,HB] norm:     ", res2["max_fermionic_HA_HB_commutator"])
    print("Thm 2 ferm gamma_loc err:    ", res2["max_fermionic_gamma_loc_error"])
    print("Thm 2 ferm exact 4D err:     ", res2["max_fermionic_exact_error"])
    print("Thm 2 bosonic Fock rel err:  ", res2["max_bosonic_trunc_rel_error"])
    print("Thm 2 redshift vis(s=2):     ", res2["proportional_redshift_dephasing_example"]["sigma_x_visibility_s2"])
    print("Thm 2 nonunital fixed-pt:    ", res2["nonunital_gksl_fixed_point_check"])
    for k in ["d=2", "d=3", "d=4", "d=5"]:
        v = res3[k]
        print(f"Thm 3 {k}: Choi_marg_err={v['valid_choi_marginal_error']:.2e}, FA*=FB*={v['valid_choi_saturation_FA']:.6f}, prod_FB={v['product_state_FB_actual_1_over_d2']:.6f}, kay_viol={v['random_max_kay_curved_violation']:.2e}")
    print("Thm 4 spectral decay err:    ", res45["double_uncertainty"]["max_spectral_block_decay_error"])
    print("Thm 4 Pythagorean err:       ", res45["double_uncertainty"]["pythagorean_error"])
    print("Thm 4 vN decomp err:         ", res45["double_uncertainty"]["vn_decomposition_error"])
    print("Thm 5 Petz-vs-Kraus diff:    ", res45["petz_formula_vs_explicit_kraus_max_diff"])
    for k, v in res45["bottleneck_checks"].items():
        print(f"Thm 5 {k}: k_enc={v['encoder_kraus_count']}, max_TP={max(v['max_TP_residual_E'], v['max_TP_residual_R']):.2e}, rand_max={v['max_random_Fe']:.6f}, bound={v['theoretical_bound']:.6f}")
    ym = res45["su2_ym_companion_galerkin"]
    print("Companion SU(2) YM Galerkin: ", [round(x, 6) for x in ym["galerkin_singlet_energies"]], f"(5v6 diff={ym['galerkin_cutoff_5_vs_6_diff']:.2e}, mat_diff={ym['naive_vs_galerkin_singlet_matrix_frob_diff']:.6f}, eval_diff={ym['naive_vs_galerkin_eigenvalue_vec_l2_diff']:.6f})")
    ev = res45["unified_two_window_evaporation"]
    print("Two-window [KB,Hdyn] max:    ", ev["max_comm_KB_Hdyn_norm"], "intra-win [H1,rho0]:", round(ev["intra_window_t_comm_norm"], 4), "max s-diss:", ev["max_window1_s_dissipation_over_page_curve"])
    print("Page curve S_rad (bits):     ", [round(x, 4) for x in ev["S_rad_vn_bits"]])
    print("Page curve F_rad(k=0..8):    ", [round(x, 4) for x in ev["F_rad_petz"]])
    print("Page curve F_bh(k=0..8):     ", [round(x, 4) for x in ev["F_bh_petz"]])
    print("Page curve max F_sum:        ", round(ev["max_F_sum"], 6), "(bound 1.5)")
    print("Saved JSON:", out_path)
    print("Saved figures:", sorted(p.name for p in FIG_DIR.glob("*.pdf")))


if __name__ == "__main__":
    main()
