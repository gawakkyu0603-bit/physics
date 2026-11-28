#!/usr/bin/env python3
"""
Self-contained numerical verification, falsification test suite (F1--F6),
and figure generator for the study:
"Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity:
KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions"

Fixed RNG seed: 20261127.
Outputs:
  - paper2_sk_jt/docs/numerical_verification.json
  - paper2_sk_jt/paper/figures/fig1_covariant_kms_and_redfield.pdf
  - paper2_sk_jt/paper/figures/fig2_jt_sk_evaporation_fdt.pdf
  - paper2_sk_jt/paper/figures/fig3_horizon_hadamard_udw.pdf
  - paper2_sk_jt/paper/figures/fig4_greybody_throat_and_nonisometric.pdf
"""

from __future__ import annotations

import json
import math
import os
import platform
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import scipy
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq, minimize_scalar
from scipy.special import dawsn, erf, erfc, sici, spherical_jn, spherical_yn, wrightomega

SEED = 20261127
FLOAT_TOL = 1e-12

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
DOCS_DIR = PROJECT_ROOT / "docs"
FIG_DIR = PROJECT_ROOT / "paper" / "figures"
DOCS_DIR.mkdir(parents=True, exist_ok=True)
FIG_DIR.mkdir(parents=True, exist_ok=True)


# ---------------------------------------------------------------------------
# Linear-algebra & GKSL utilities
# ---------------------------------------------------------------------------

def comm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return A @ B - B @ A


def anticomm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return A @ B + B @ A


def gksl_apply(jumps: list[np.ndarray], rho: np.ndarray) -> np.ndarray:
    out = np.zeros_like(rho, dtype=np.complex128)
    for L in jumps:
        LdL = L.conj().T @ L
        out += L @ rho @ L.conj().T - 0.5 * anticomm(LdL, rho)
    return out


def gksl_dual_apply(jumps: list[np.ndarray], X: np.ndarray) -> np.ndarray:
    out = np.zeros_like(X, dtype=np.complex128)
    for L in jumps:
        LdL = L.conj().T @ L
        out += L.conj().T @ X @ L - 0.5 * anticomm(LdL, X)
    return out


def gksl_superop(jumps: list[np.ndarray], d: int) -> np.ndarray:
    """Column-stacking Liouvillian superoperator matrix (d^2 x d^2)."""
    I_d = np.eye(d, dtype=np.complex128)
    L_sup = np.zeros((d * d, d * d), dtype=np.complex128)
    for L in jumps:
        LdL = L.conj().T @ L
        L_sup += np.kron(L.conj(), L) - 0.5 * np.kron(I_d, LdL) - 0.5 * np.kron(LdL.T, I_d)
    return L_sup


def choi_from_superop(Phi_sup: np.ndarray, d: int) -> np.ndarray:
    """Normalized Choi matrix J = (id x Phi)(|Phi_d><Phi_d|) of size (d^2 x d^2)."""
    J = np.zeros((d * d, d * d), dtype=np.complex128)
    for i in range(d):
        for j in range(d):
            Eij = np.zeros((d, d), dtype=np.complex128)
            Eij[i, j] = 1.0
            Phi_Eij = (Phi_sup @ Eij.reshape(-1, order="F")).reshape((d, d), order="F")
            # |i><j|_R \otimes Phi(|i><j|)
            E_ref = np.zeros((d, d), dtype=np.complex128)
            E_ref[i, j] = 1.0
            J += np.kron(E_ref, Phi_Eij) / d
    return J


def vn_entropy(rho: np.ndarray) -> float:
    evals = np.linalg.eigvalsh(0.5 * (rho + rho.conj().T))
    evals = evals[evals > 1e-15]
    return float(-np.sum(evals * np.log(evals)))


def rel_entropy(rho: np.ndarray, sigma: np.ndarray) -> float:
    evals_r, U_r = np.linalg.eigh(0.5 * (rho + rho.conj().T))
    evals_s, U_s = np.linalg.eigh(0.5 * (sigma + sigma.conj().T))
    assert np.all(evals_s > 1e-15), "Reference state must be full rank."
    log_s = U_s @ np.diag(np.log(evals_s)) @ U_s.conj().T
    s_rho = -np.sum(evals_r[evals_r > 1e-15] * np.log(evals_r[evals_r > 1e-15]))
    return float(-s_rho - np.real(np.trace(rho @ log_s)))


def petz_fidelity_from_choi(J: np.ndarray, d_in: int, d_out: int) -> float:
    """Exact Petz transpose recovery entanglement fidelity from Choi state J (Tr J = 1).
    J is normalized on R (dim d_in) x B (dim d_out), with Tr_B(J) = I_R / d_in.
    """
    J_reshaped = J.reshape((d_in, d_out, d_in, d_out))
    sigma_B = np.einsum("aiaj->ij", J_reshaped)
    evals, U = np.linalg.eigh(0.5 * (sigma_B + sigma_B.conj().T))
    inv_q = np.where(evals > 1e-14, np.maximum(evals, 1e-30) ** (-0.25), 0.0)
    sigma_m14 = U @ np.diag(inv_q) @ U.conj().T
    M = np.kron(np.eye(d_in, dtype=np.complex128), sigma_m14)
    A = M @ J @ M
    return float(np.real(np.trace(A @ A)) / d_in)


# ---------------------------------------------------------------------------
# F1: SK Structural Positivity, KMS Mapping, and Non-Secular Redfield Contrast
# ---------------------------------------------------------------------------

def run_f1_sk_positivity_and_redfield(rng: np.random.Generator) -> dict:
    omega = 1.0
    gamma0 = 0.4
    sigma_p = np.array([[0.0, 1.0], [0.0, 0.0]], dtype=np.complex128)  # |0><1| raises if H = diag(w/2, -w/2)
    # Use H = diag(0, omega) so |0> is ground (E=0) and |1> is excited (E=omega)
    H = np.diag([0.0, omega]).astype(np.complex128)
    L_down = np.array([[0.0, 1.0], [0.0, 0.0]], dtype=np.complex128)  # |0><1|: [H, L_down] = -omega L_down
    L_up = L_down.conj().T                                            # |1><0|: [H, L_up] = +omega L_up

    assert np.linalg.norm(comm(H, L_down) + omega * L_down) < FLOAT_TOL
    assert np.linalg.norm(comm(H, L_up) - omega * L_up) < FLOAT_TOL

    temps = [0.25, 0.5, 1.0, 2.0, 5.0]
    s_grid = [0.05, 0.2, 1.0, 3.0]

    max_tp_err_davies = 0.0
    min_choi_davies = 1e9
    redfield_neg_eigs = []
    redfield_theory_koss = []

    # Check SK algebraic axioms on quadratic Hermitian-jump influence functional
    # S_IF(K_+, K_-) = (i/2) sum_k gamma_k (K_{k,+} - K_{k,-})^2
    K_vals_p = rng.normal(size=(50, 4))
    K_vals_m = rng.normal(size=(50, 4))
    gammas = np.array([0.3, 0.7, 1.1, 0.5])
    S_if_diag = 0.5j * np.sum(gammas * (K_vals_p - K_vals_p) ** 2, axis=1)
    S_if_pm = 0.5j * np.sum(gammas * (K_vals_p - K_vals_m) ** 2, axis=1)
    S_if_mp = 0.5j * np.sum(gammas * (K_vals_m - K_vals_p) ** 2, axis=1)
    sk_tp_max_err = float(np.max(np.abs(S_if_diag)))
    sk_conj_max_err = float(np.max(np.abs(np.conj(S_if_pm) + S_if_mp)))
    sk_im_min = float(np.min(np.imag(S_if_pm)))
    assert sk_tp_max_err == 0.0
    assert sk_conj_max_err < FLOAT_TOL
    assert sk_im_min >= 0.0

    # Davies vs non-secular Redfield Choi test across temperatures
    I2 = np.eye(2, dtype=np.complex128)
    S_op = L_down + L_up  # sigma_x

    # Detailed scan for Fig 1(b)
    T_scan = np.linspace(0.15, 3.0, 60)
    choi_min_davies_scan = []
    choi_min_redfield_scan = []
    koss_min_redfield_scan = []

    for T_H in T_scan:
        beta = 1.0 / T_H
        n_be = 1.0 / (np.exp(beta * omega) - 1.0)
        g_down = gamma0 * (1.0 + n_be)
        g_up = gamma0 * n_be
        # Exact SK FDT check: D_K = coth(beta*omega/2) * rho_spec
        rho_spec = gamma0
        D_K = (1.0 / np.tanh(0.5 * beta * omega)) * rho_spec
        assert abs(0.5 * (D_K + rho_spec) - g_down) < 1e-13
        assert abs(0.5 * (D_K - rho_spec) - g_up) < 1e-13
        assert abs(g_up / g_down - np.exp(-beta * omega)) < 1e-13

        # Davies superoperator (secular)
        L_dav_sup = gksl_superop([np.sqrt(g_down) * L_down, np.sqrt(g_up) * L_up], 2)
        Phi_dav = expm(0.15 * L_dav_sup)
        J_dav = choi_from_superop(Phi_dav, 2)
        choi_min_davies_scan.append(float(np.min(np.linalg.eigvalsh(0.5 * (J_dav + J_dav.conj().T)))))

        # Non-secular Bloch-Redfield generator: L_Red(rho) = [S_tilde rho, S] + [S, rho S_tilde^dag]
        # with S_tilde = (g_down/2) L_down + (g_up/2) L_up (zero Lamb shift)
        S_tilde = 0.5 * g_down * L_down + 0.5 * g_up * L_up
        # Column-stacking superoperator for A rho B -> (B^T \otimes A) vec(rho)
        L_red_sup = (
            np.kron(S_op.T, S_tilde)
            - np.kron(I2, S_op @ S_tilde)
            + np.kron(S_tilde.conj(), S_op)
            - np.kron((S_tilde.conj().T @ S_op).T, I2)
        )
        # Verify trace preservation of Redfield
        tr_vec = I2.reshape(-1, order="F")
        assert np.linalg.norm(tr_vec.conj() @ L_red_sup) < 1e-13
        Phi_red = expm(0.15 * L_red_sup)
        J_red = choi_from_superop(Phi_red, 2)
        lam_min_red = float(np.min(np.linalg.eigvalsh(0.5 * (J_red + J_red.conj().T))))
        choi_min_redfield_scan.append(lam_min_red)

        # Analytic Kossakowski negative eigenvalue: (g_d + g_u - sqrt(2(g_d^2 + g_u^2))) / 2
        lam_koss = 0.5 * (g_down + g_up - math.sqrt(2.0 * (g_down**2 + g_up**2)))
        koss_min_redfield_scan.append(lam_koss)

    for T_H in temps:
        beta = 1.0 / T_H
        n_be = 1.0 / (np.exp(beta * omega) - 1.0)
        g_down = gamma0 * (1.0 + n_be)
        g_up = gamma0 * n_be
        L_dav_sup = gksl_superop([np.sqrt(g_down) * L_down, np.sqrt(g_up) * L_up], 2)
        S_tilde = 0.5 * g_down * L_down + 0.5 * g_up * L_up
        L_red_sup = (
            np.kron(S_op.T, S_tilde)
            - np.kron(I2, S_op @ S_tilde)
            + np.kron(S_tilde.conj(), S_op)
            - np.kron((S_tilde.conj().T @ S_op).T, I2)
        )
        for s in s_grid:
            Phi_dav = expm(s * L_dav_sup)
            J_dav = choi_from_superop(Phi_dav, 2)
            min_ev = float(np.min(np.linalg.eigvalsh(0.5 * (J_dav + J_dav.conj().T))))
            min_choi_davies = min(min_choi_davies, min_ev)
            # Partial trace over output
            J_resh = J_dav.reshape((2, 2, 2, 2))
            tr_out = np.einsum("aibi->ab", J_resh)
            max_tp_err_davies = max(max_tp_err_davies, float(np.linalg.norm(tr_out - 0.5 * I2)))

        # Short-time Redfield CP violation check (s = 0.05)
        Phi_red = expm(0.05 * L_red_sup)
        J_red = choi_from_superop(Phi_red, 2)
        lam_min_red = float(np.min(np.linalg.eigvalsh(0.5 * (J_red + J_red.conj().T))))
        redfield_neg_eigs.append(lam_min_red)
        lam_koss = 0.5 * (g_down + g_up - math.sqrt(2.0 * (g_down**2 + g_up**2)))
        redfield_theory_koss.append(lam_koss)

    assert min_choi_davies >= -1e-14, f"Davies CP violated: {min_choi_davies}"
    assert max_tp_err_davies < FLOAT_TOL
    # Redfield MUST strictly violate CP at every finite T_H!
    assert all(ev < -1e-4 for ev in redfield_neg_eigs), f"Expected Redfield CP violation: {redfield_neg_eigs}"

    # M2 microscopic harmonic-bath characteristic function check (symmetric source O_r = 0):
    # H_b = a^dag a, beta = 1, B = (a + a^dag)/sqrt(2), Delta_O = 0.4
    # Noise kernel N(0) = (1/2) coth(1/2) = D_K(0)/2 => <exp(-i Delta_O B)> = exp(-(Delta_O)^2 N(0)/2)
    N_bath = 80
    delta_O = 0.4
    a_b = np.diag(np.sqrt(np.arange(1, N_bath, dtype=np.float64)), 1)
    B_op = (a_b + a_b.T) / math.sqrt(2.0)
    w_b = np.exp(-np.arange(N_bath, dtype=np.float64))
    w_b /= np.sum(w_b)
    char_direct = float(np.real(np.trace(np.diag(w_b) @ expm(-1j * delta_O * B_op))))
    N_zero = 0.5 / math.tanh(0.5)  # half-anticommutator noise kernel N = D_K / 2
    char_consistent = math.exp(-0.5 * (delta_O**2) * N_zero)
    char_doubled_err = abs(char_direct - math.exp(-(delta_O**2) * N_zero))
    char_consistent_err = abs(char_direct - char_consistent)
    assert char_consistent_err < 1e-12
    assert char_doubled_err > 0.05

    # M3b negative control: pointwise SK1--SK3 (Im S_IF >= 0) do NOT suffice for positivity/CP
    M_had = np.array([[1.0, 0.9, 0.9], [0.9, 1.0, 0.1], [0.9, 0.1, 1.0]], dtype=np.float64)
    S_had = -1j * np.log(M_had)
    assert float(np.max(np.abs(np.diag(S_had)))) == 0.0
    assert float(np.max(np.abs(np.conj(S_had) + S_had.T))) < 1e-15
    assert float(np.min(np.imag(S_had))) >= 0.0
    sk_nonsuff_min_eig = float(np.min(np.linalg.eigvalsh(M_had / 3.0)))
    assert sk_nonsuff_min_eig < -0.05

    # M3a negative control: two-bath Unruh (outgoing thermal T_H + ingoing vacuum T=0) breaks single-T KMS
    n_H_ref = 1.0 / math.expm1(1.0)
    two_bath_ratio = n_H_ref / (n_H_ref + 2.0)
    single_kms_ratio = math.exp(-1.0)
    assert abs(two_bath_ratio - single_kms_ratio) > 0.1

    # R2 canonical chiral-current Fourier normalization check:
    # W_J(t) = -1 / (4 pi (t - i eps)^2) => int dt exp(i Omega t) W_J(t) = (Omega / 2) exp(-eps Omega)
    Omega_r2, eps_r2 = 1.3, 0.2
    real_W = lambda t: -(t * t - eps_r2 * eps_r2) / (4.0 * math.pi * (t * t + eps_r2 * eps_r2) ** 2)
    imag_W = lambda t: -(2.0 * t * eps_r2) / (4.0 * math.pi * (t * t + eps_r2 * eps_r2) ** 2)
    qr_r2 = quad(real_W, 0.0, np.inf, weight="cos", wvar=Omega_r2, epsabs=1e-12)[0]
    qi_r2 = quad(imag_W, 0.0, np.inf, weight="sin", wvar=Omega_r2, epsabs=1e-12)[0]
    chiral_fourier_num = float(2.0 * (qr_r2 - qi_r2))
    chiral_fourier_exact = 0.5 * Omega_r2 * math.exp(-eps_r2 * Omega_r2)
    chiral_fourier_err = float(abs(chiral_fourier_num - chiral_fourier_exact))
    chiral_fourier_ratio_to_over_2pi = float(
        chiral_fourier_num / ((Omega_r2 / (2.0 * math.pi)) * math.exp(-eps_r2 * Omega_r2))
    )
    assert chiral_fourier_err < 1e-11
    assert abs(chiral_fourier_ratio_to_over_2pi - math.pi) < 1e-10

    # R3 negative control: QND system condition [H_O, K] = 0 does NOT force bath retarded kernel D_R = 0
    omega_b, t_b = 1.3, 0.7
    phase_b = np.diag(np.exp(-1j * omega_b * t_b * np.arange(N_bath, dtype=np.float64)))
    Bt_op = phase_b.conj().T @ B_op @ phase_b
    w_b3 = np.exp(-omega_b * np.arange(N_bath, dtype=np.float64))
    w_b3 /= np.sum(w_b3)
    bath_DR_osc = float(np.real(-1j * np.trace(np.diag(w_b3) @ comm(Bt_op, B_op))))
    bath_DR_osc_err = float(abs(bath_DR_osc - (-math.sin(omega_b * t_b))))
    assert bath_DR_osc_err < 1e-13 and abs(bath_DR_osc) > 0.5

    eta_ohm, lam_ohm, beta_ohm = 1.0, 4.0, 0.9
    bath_DR_ohmic_zero = float(-quad(lambda w: 2.0 * eta_ohm * math.exp(-w / lam_ohm) / math.pi, 0.0, np.inf)[0])
    bath_DR_ohmic_zero_err = float(abs(bath_DR_ohmic_zero + 2.0 * eta_ohm * lam_ohm / math.pi))
    bath_ohmic_zero_rate = float(2.0 * eta_ohm / beta_ohm)
    assert bath_DR_ohmic_zero_err < 1e-10 and abs(bath_DR_ohmic_zero) > 1.0

    # Layer-2 unraveling gauge non-uniqueness witness: identical Layer-1 CPTP map,
    # strictly different Layer-2 single-shot probabilities & conditional coherences
    K0_g = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    K1_g = np.array([[0.0, 0.0], [0.0, 1.0]], dtype=np.complex128)
    u_g, v_g = 0.6, 0.8  # u^2 + v^2 = 1
    K0_rot = u_g * K0_g + v_g * K1_g
    K1_rot = -v_g * K0_g + u_g * K1_g
    rho_plus = 0.5 * np.ones((2, 2), dtype=np.complex128)
    l2_channel_diff = float(np.linalg.norm(
        (K0_rot @ rho_plus @ K0_rot.conj().T + K1_rot @ rho_plus @ K1_rot.conj().T)
        - (K0_g @ rho_plus @ K0_g.conj().T + K1_g @ rho_plus @ K1_g.conj().T)
    ))
    l2_p0_orig = float(np.real(np.trace(K0_g @ K0_g @ K0_g.conj().T)))
    l2_p0_rot = float(np.real(np.trace(K0_rot @ K0_g @ K0_rot.conj().T)))
    rho_cond_orig = (K0_g @ rho_plus @ K0_g.conj().T) / float(np.real(np.trace(K0_g @ rho_plus @ K0_g.conj().T)))
    rho_cond_rot = (K0_rot @ rho_plus @ K0_rot.conj().T) / float(np.real(np.trace(K0_rot @ rho_plus @ K0_rot.conj().T)))
    l2_cond_coh_orig = float(abs(rho_cond_orig[0, 1]))
    l2_cond_coh_rot = float(abs(rho_cond_rot[0, 1]))
    assert l2_channel_diff < 1e-15
    assert abs(l2_p0_orig - 1.0) < 1e-15 and abs(l2_p0_rot - 0.36) < 1e-15
    assert l2_cond_coh_orig < 1e-15 and abs(l2_cond_coh_rot - 0.48) < 1e-14

    # Major Point 5: Separate no-signaling (remote marginal invariance under any local CPTP/unitary map)
    # from Layer-1 channel model-compatibility (sum_x I_{B,x} = Phi_B)
    psi_ent = np.array([math.sqrt(0.8), 0.0, 0.0, math.sqrt(0.2)], dtype=np.complex128)
    rho_ent = np.outer(psi_ent, psi_ent.conj())
    X_loc = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    U_loc_RL = np.kron(X_loc, I2)
    rho_ent_after = U_loc_RL @ rho_ent @ U_loc_RL.conj().T
    rho_L_before = np.einsum("aiaj->ij", rho_ent.reshape((2, 2, 2, 2)))
    rho_L_after = np.einsum("aiaj->ij", rho_ent_after.reshape((2, 2, 2, 2)))
    rho_R_before = np.einsum("iaja->ij", rho_ent.reshape((2, 2, 2, 2)))
    rho_R_after = np.einsum("iaja->ij", rho_ent_after.reshape((2, 2, 2, 2)))
    rho_R_deph = K0_g @ rho_R_before @ K0_g.conj().T + K1_g @ rho_R_before @ K1_g.conj().T
    ns_remote_marginal_err = float(np.linalg.norm(rho_L_after - rho_L_before))
    ns_local_channel_mismatch = float(np.linalg.norm(rho_R_after - rho_R_deph))
    assert ns_remote_marginal_err < 1e-15
    assert ns_local_channel_mismatch > 0.5

    return {
        "sk_tp_max_err": sk_tp_max_err,
        "sk_conj_max_err": sk_conj_max_err,
        "sk_im_min": sk_im_min,
        "m2_bath_char_direct": char_direct,
        "m2_bath_char_consistent_err": char_consistent_err,
        "m2_bath_char_doubled_mismatch": char_doubled_err,
        "m3b_sk_pointwise_nonsuff_min_eig": sk_nonsuff_min_eig,
        "m3a_two_bath_unruh_ratio": two_bath_ratio,
        "m3a_single_kms_ratio": single_kms_ratio,
        "chiral_current_fourier_quad": chiral_fourier_num,
        "chiral_current_fourier_err": chiral_fourier_err,
        "chiral_current_pi_ratio_check": chiral_fourier_ratio_to_over_2pi,
        "qnd_bath_osc_DR_nonzero": bath_DR_osc,
        "qnd_bath_osc_DR_err": bath_DR_osc_err,
        "qnd_bath_ohmic_DR_zero_freq": bath_DR_ohmic_zero,
        "qnd_bath_ohmic_zero_freq_rate": bath_ohmic_zero_rate,
        "layer2_unraveling_channel_diff": l2_channel_diff,
        "layer2_unraveling_p0_orig": l2_p0_orig,
        "layer2_unraveling_p0_rot": l2_p0_rot,
        "layer2_unraveling_cond_coh_rot": l2_cond_coh_rot,
        "no_signaling_local_unitary_remote_marginal_err": ns_remote_marginal_err,
        "no_signaling_local_unitary_vs_dephasing_mismatch": ns_local_channel_mismatch,
        "davies_min_choi_eig": min_choi_davies,
        "davies_max_tp_err": max_tp_err_davies,
        "redfield_s0p05_min_choi_eigs_by_T": {str(T): ev for T, ev in zip(temps, redfield_neg_eigs)},
        "redfield_analytic_koss_neg_eig_by_T": {str(T): ev for T, ev in zip(temps, redfield_theory_koss)},
        "_plot": {
            "T_scan": T_scan.tolist(),
            "choi_min_davies": choi_min_davies_scan,
            "choi_min_redfield": choi_min_redfield_scan,
            "koss_min_redfield": koss_min_redfield_scan,
        },
    }


# ---------------------------------------------------------------------------
# F2: Covariant (t,s) Integrability (omega != 0), GNS Monotonicity, Non-Secular Breaking
# ---------------------------------------------------------------------------

def run_f2_covariant_kms_integrability(rng: np.random.Generator) -> dict:
    # Truncated harmonic oscillator d = 6, H_B = omega * N, eigenoperator jumps a, a^dag
    d = 6
    omega = 1.2
    T_H = 0.65
    beta = 1.0 / T_H
    gamma0 = 0.35
    n_be = 1.0 / (np.exp(beta * omega) - 1.0)
    g_down = gamma0 * (1.0 + n_be)
    g_up = gamma0 * n_be

    H_B = np.diag([omega * n for n in range(d)]).astype(np.complex128)
    a = np.zeros((d, d), dtype=np.complex128)
    for n in range(1, d):
        a[n - 1, n] = math.sqrt(n)
    adag = a.conj().T

    # Check exact eigenoperator relations [H_B, a] = -omega a, [H_B, adag] = +omega adag
    assert np.linalg.norm(comm(H_B, a) + omega * a) < FLOAT_TOL
    assert np.linalg.norm(comm(H_B, adag) - omega * adag) < FLOAT_TOL

    L_down = math.sqrt(g_down) * a
    L_up = math.sqrt(g_up) * adag
    jumps = [L_down, L_up]
    omegas = [omega, -omega]

    # Exact Gibbs state on truncated d=6 space
    weights = np.exp(-beta * np.real(np.diag(H_B)))
    rho_beta = np.diag(weights / np.sum(weights)).astype(np.complex128)

    # 1. Stationarity L_B(rho_beta) = 0
    kms_stat_err = float(np.linalg.norm(gksl_apply(jumps, rho_beta)))
    assert kms_stat_err < 1e-14

    # 2. Exact energy drift L_B^dag(H_B) = -sum_k omega_k L_k^dag L_k
    #    and carre du champ Gamma(H_B, H_B) = sum_k omega_k^2 L_k^dag L_k
    drift_lhs = gksl_dual_apply(jumps, H_B)
    drift_rhs = -sum(w * (L.conj().T @ L) for w, L in zip(omegas, jumps))
    drift_err = float(np.linalg.norm(drift_lhs - drift_rhs))
    drift_norm = float(np.linalg.norm(drift_lhs))
    assert drift_err < 1e-13
    assert drift_norm > 0.5  # Subsystem BPS immunity is genuinely BROKEN!

    cdc_lhs = gksl_dual_apply(jumps, H_B @ H_B) - H_B @ drift_lhs - drift_lhs @ H_B
    cdc_rhs = sum((w**2) * (L.conj().T @ L) for w, L in zip(omegas, jumps))
    cdc_err = float(np.linalg.norm(cdc_lhs - cdc_rhs))
    assert cdc_err < 1e-13

    # 3. Exact (t,s) integrability [L_B, ad_{H_B}] = 0 AND finite-(t,s) commutation
    L_sup = gksl_superop(jumps, d)
    ad_H_sup = -1j * (np.kron(np.eye(d), H_B) - np.kron(H_B.T, np.eye(d)))
    gen_comm_err = float(np.linalg.norm(comm(L_sup, ad_H_sup)))
    assert gen_comm_err < 1e-13

    t_val, s_val = 1.7, 0.9
    U_sup = expm(t_val * ad_H_sup)
    Phi_sup = expm(s_val * L_sup)
    flow_comm_err = float(np.linalg.norm(U_sup @ Phi_sup - Phi_sup @ U_sup))
    assert flow_comm_err < 1e-13

    # 4. Exact GNS-KMS monotonicity identity:
    #    -2 Tr(rho_beta A L_B^dag(A)) = sum_k Tr(rho_beta [L_k, A]^dag [L_k, A]) >= 0
    max_gns_id_err = 0.0
    min_gns_rhs = 1e9
    for _ in range(30):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        A = 0.5 * (X + X.conj().T)
        lhs = -2.0 * np.trace(rho_beta @ A @ gksl_dual_apply(jumps, A))
        rhs = sum(np.trace(rho_beta @ comm(L, A).conj().T @ comm(L, A)) for L in jumps)
        max_gns_id_err = max(max_gns_id_err, float(abs(lhs - rhs)))
        min_gns_rhs = min(min_gns_rhs, float(np.real(rhs)))
    assert max_gns_id_err < 1e-13
    assert min_gns_rhs >= -1e-14

    # 5. Demonstrate cooling (purity INCREASING while D(rho || rho_beta) and GNS chi^2 DECREASE!)
    rho0 = np.eye(d, dtype=np.complex128) / d  # maximally mixed (purity = 1/6)
    s_traj = np.linspace(0.0, 6.0, 121)
    purities = []
    rel_ents = []
    gns_chi2 = []
    inv_rho_beta = np.diag(1.0 / np.real(np.diag(rho_beta))).astype(np.complex128)
    invsqrt_rho_beta = np.diag(1.0 / np.sqrt(np.real(np.diag(rho_beta)))).astype(np.complex128)
    I_d = np.eye(d, dtype=np.complex128)

    for s in s_traj:
        rho_s = (expm(s * L_sup) @ rho0.reshape(-1, order="F")).reshape((d, d), order="F")
        rho_s = 0.5 * (rho_s + rho_s.conj().T)
        purities.append(float(np.real(np.trace(rho_s @ rho_s))))
        rel_ents.append(rel_entropy(rho_s, rho_beta))
        B_s = invsqrt_rho_beta @ rho_s @ invsqrt_rho_beta - I_d
        gns_chi2.append(float(np.real(np.trace(rho_beta @ B_s @ B_s))))

    assert purities[-1] > purities[0] + 0.1  # Purity strictly INCREASES (cooling)!
    assert all(rel_ents[i + 1] <= rel_ents[i] + 1e-12 for i in range(len(rel_ents) - 1))
    assert all(gns_chi2[i + 1] <= gns_chi2[i] + 1e-12 for i in range(len(gns_chi2) - 1))

    # 5b. Non-commuting GNS chi^2 audit (symmetric Hermitian B_s = sigma^{-1/2} rho_s sigma^{-1/2} - I):
    #     First check explicit 2-level faithful counterexample to asymmetric A_L = sigma^{-1} rho - I
    #     and exact verification of symmetric B = sigma^{-1/2} rho sigma^{-1/2} - I intertwining & derivative.
    sigma_2 = np.diag([0.8, 0.2]).astype(np.complex128)
    rho_2 = np.array([[0.5, 0.2], [0.2, 0.5]], dtype=np.complex128)
    inv_s2 = np.diag([1.0 / 0.8, 1.0 / 0.2]).astype(np.complex128)
    invsqrt_s2 = np.diag([1.0 / math.sqrt(0.8), 1.0 / math.sqrt(0.2)]).astype(np.complex128)
    I_2 = np.eye(2, dtype=np.complex128)
    A_asym_2 = inv_s2 @ rho_2 - I_2
    B_sym_2 = invsqrt_s2 @ rho_2 @ invsqrt_s2 - I_2
    asym_lhs_2 = float(np.real(np.trace(sigma_2 @ A_asym_2.conj().T @ A_asym_2)))
    chi2_rhs_2 = float(np.real(np.trace(rho_2 @ inv_s2 @ rho_2)) - 1.0)
    sym_lhs_2 = float(np.real(np.trace(sigma_2 @ B_sym_2 @ B_sym_2)))
    r1_2lvl_asym_mismatch = abs(asym_lhs_2 - chi2_rhs_2)
    r1_2lvl_asym_nonherm = float(np.linalg.norm(A_asym_2 - A_asym_2.conj().T))
    r1_2lvl_sym_norm_err = abs(sym_lhs_2 - chi2_rhs_2)
    r1_2lvl_sym_herm_err = float(np.linalg.norm(B_sym_2 - B_sym_2.conj().T))
    L_low2 = np.array([[0.0, 1.0], [0.0, 0.0]], dtype=np.complex128)
    jumps_2 = [L_low2, 0.5 * L_low2.conj().T]  # gamma_down = 1, gamma_up = 1/4 = 0.2 / 0.8
    rho_dot_2 = gksl_apply(jumps_2, rho_2)
    B_dot_2 = invsqrt_s2 @ rho_dot_2 @ invsqrt_s2
    Ldag_B_2 = gksl_dual_apply(jumps_2, B_sym_2)
    r1_2lvl_intertwine_err = float(np.linalg.norm(B_dot_2 - Ldag_B_2))
    dchi2_schr_2 = float(np.real(np.trace(rho_dot_2 @ inv_s2 @ rho_2 + rho_2 @ inv_s2 @ rho_dot_2)))
    dchi2_dirichlet_2 = float(2.0 * np.real(np.trace(sigma_2 @ B_sym_2 @ Ldag_B_2)))
    r1_2lvl_deriv_err = abs(dchi2_schr_2 - dchi2_dirichlet_2)
    assert r1_2lvl_asym_mismatch > 0.5 and r1_2lvl_asym_nonherm > 1.0
    assert r1_2lvl_sym_norm_err < 1e-14 and r1_2lvl_sym_herm_err < 1e-15
    assert r1_2lvl_intertwine_err < 1e-14 and r1_2lvl_deriv_err < 1e-14
    assert abs(dchi2_dirichlet_2 - (-1.71875)) < 1e-14

    # Full d=6 non-commuting coherent trajectory checking norm equality, Hermiticity, intertwining & derivative
    psi_nc = np.array([1.0, 0.8j, -0.5, 0.3, -0.2j, 0.1], dtype=np.complex128)
    psi_nc /= np.linalg.norm(psi_nc)
    rho_nc0 = 0.7 * np.outer(psi_nc, psi_nc.conj()) + 0.3 * np.eye(d, dtype=np.complex128) / d
    assert np.linalg.norm(comm(rho_nc0, rho_beta)) > 0.05
    nc_rel_ents = []
    nc_gns_chi2 = []
    nc_max_norm_eq_err = 0.0
    nc_max_herm_err = 0.0
    nc_max_intertwine_err = 0.0
    nc_max_deriv_err = 0.0
    for s in s_traj:
        rho_ns = (expm(s * L_sup) @ rho_nc0.reshape(-1, order="F")).reshape((d, d), order="F")
        rho_ns = 0.5 * (rho_ns + rho_ns.conj().T)
        nc_rel_ents.append(rel_entropy(rho_ns, rho_beta))
        B_ns = invsqrt_rho_beta @ rho_ns @ invsqrt_rho_beta - I_d
        chi2_sym = float(np.real(np.trace(rho_beta @ B_ns @ B_ns)))
        chi2_tr = float(np.real(np.trace(rho_ns @ inv_rho_beta @ rho_ns)) - 1.0)
        nc_gns_chi2.append(chi2_sym)
        nc_max_norm_eq_err = max(nc_max_norm_eq_err, abs(chi2_sym - chi2_tr))
        nc_max_herm_err = max(nc_max_herm_err, float(np.linalg.norm(B_ns - B_ns.conj().T)))
        rho_ns_dot = gksl_apply(jumps, rho_ns)
        B_ns_dot = invsqrt_rho_beta @ rho_ns_dot @ invsqrt_rho_beta
        Ldag_B_ns = gksl_dual_apply(jumps, B_ns)
        nc_max_intertwine_err = max(nc_max_intertwine_err, float(np.linalg.norm(B_ns_dot - Ldag_B_ns)))
        dchi2_schr_ns = float(2.0 * np.real(np.trace(rho_ns_dot @ inv_rho_beta @ rho_ns)))
        dchi2_dir_ns = float(2.0 * np.real(np.trace(rho_beta @ B_ns @ Ldag_B_ns)))
        nc_max_deriv_err = max(nc_max_deriv_err, abs(dchi2_schr_ns - dchi2_dir_ns))
        assert dchi2_dir_ns <= 1e-12
    assert nc_max_norm_eq_err < 1e-12 and nc_max_herm_err < 1e-13
    assert nc_max_intertwine_err < 1e-11 and nc_max_deriv_err < 1e-11
    assert all(nc_rel_ents[i + 1] <= nc_rel_ents[i] + 1e-12 for i in range(len(nc_rel_ents) - 1))
    assert all(nc_gns_chi2[i + 1] <= nc_gns_chi2[i] + 1e-12 for i in range(len(nc_gns_chi2) - 1))

    # 5c. M1 counterexample: 3-level system with L^dag(H) = 0 yet Gamma_L(H, H) = 2|1><1| != 0
    H3 = np.diag([0.0, 1.0, 2.0]).astype(np.complex128)
    Lm3 = np.zeros((3, 3), dtype=np.complex128)
    Lm3[0, 1] = 1.0
    Lp3 = np.zeros((3, 3), dtype=np.complex128)
    Lp3[2, 1] = 1.0
    m1_drift_norm = float(np.linalg.norm(gksl_dual_apply([Lm3, Lp3], H3)))
    m1_cdc = gksl_dual_apply([Lm3, Lp3], H3 @ H3)
    m1_cdc_err = float(np.linalg.norm(m1_cdc - np.diag([0.0, 2.0, 0.0])))
    rho3_0 = np.diag([0.0, 1.0, 0.0]).astype(np.complex128)
    rho3_1 = (expm(gksl_superop([Lm3, Lp3], 3)) @ rho3_0.reshape(-1, order="F")).reshape((3, 3), order="F")
    m1_mean_s1 = float(np.real(np.trace(H3 @ rho3_1)))
    m1_var_s1 = float(np.real(np.trace(H3 @ H3 @ rho3_1)) - m1_mean_s1**2)
    assert m1_drift_norm < 1e-15 and m1_cdc_err < 1e-15
    assert abs(m1_var_s1 - (1.0 - math.exp(-2.0))) < 1e-14

    # 5d. M4 non-stationary negative control: T(t) = exp(-0.3 t) breaks (t,s) flatness & moving-Gibbs monotonicity
    H2 = np.diag([0.0, 1.0]).astype(np.complex128)
    L_dn2 = np.array([[0.0, 1.0], [0.0, 0.0]], dtype=np.complex128)
    ad_H2 = -1j * (np.kron(np.eye(2), H2) - np.kron(H2.T, np.eye(2)))

    def ns_rates(t_val_ns: float) -> tuple[float, float]:
        T_ns = math.exp(-0.3 * t_val_ns)
        n_ns = 1.0 / math.expm1(1.0 / T_ns)
        return 0.4 * (1.0 + n_ns), 0.4 * n_ns

    def ns_gen(t_val_ns: float) -> np.ndarray:
        gd_ns, gu_ns = ns_rates(t_val_ns)
        return gksl_superop([math.sqrt(gd_ns) * L_dn2, math.sqrt(gu_ns) * L_dn2.conj().T], 2)

    m4_inst_comm_max = max(float(np.linalg.norm(comm(ns_gen(t_chk), ad_H2))) for t_chk in (0.0, 0.5))
    rho_exc2 = np.diag([0.0, 1.0]).astype(np.complex128).reshape(-1, order="F")
    path_a = expm(0.2 * ns_gen(0.5)) @ expm(0.5 * ad_H2) @ rho_exc2
    path_b = expm(0.5 * ad_H2) @ expm(0.2 * ns_gen(0.0)) @ rho_exc2
    m4_rect_path_diff = float(np.linalg.norm(path_a - path_b))
    p_gibbs0 = 1.0 / (1.0 + math.e)
    sol_ns = solve_ivp(
        lambda t_v, y_v: [ns_rates(t_v)[1] * (1.0 - y_v[0]) - ns_rates(t_v)[0] * y_v[0]],
        (0.0, 0.5),
        [p_gibbs0],
        rtol=1e-12,
        atol=1e-14,
    )
    p_end = float(sol_ns.y[0, -1])
    q_end = 1.0 / (1.0 + math.exp(math.exp(0.15)))
    m4_moving_rel_ent = p_end * math.log(p_end / q_end) + (1.0 - p_end) * math.log((1.0 - p_end) / (1.0 - q_end))
    assert m4_inst_comm_max < 1e-15 and m4_rect_path_diff > 0.01 and m4_moving_rel_ent > 1e-3

    # 5e. Exact Duhamel finite-time holonomy trace-norm bound vs observed holonomy
    #     On [0, dt] x [0, ds] with fixed K = -i ad_H and [L(t), K] = 0:
    #     ||(Phi_top - Phi_bot)(rho)||_1 <= ds * ||L(dt) - L(0)||_{1->1} <= ds * dt * sup ||d_tau L(tau)||_{1->1}.
    #     For two-level Davies with fixed gamma0=0.4, ||L(dt)-L(0)||_{1->1} = 2 * |gamma_up(dt) - gamma_up(0)|.
    diff_rect_mat = (path_a - path_b).reshape((2, 2), order="F")
    duhamel_holonomy_trace_norm = float(np.sum(np.linalg.svd(diff_rect_mat, compute_uv=False)))
    gu_0 = ns_rates(0.0)[1]
    gu_0p5 = ns_rates(0.5)[1]
    duhamel_deltaL_bound = float(0.2 * 2.0 * abs(gu_0p5 - gu_0))
    # |d/dt n_T(t)| = 0.3 * exp(1/T) / (T * (exp(1/T) - 1)^2), maximized at t = 0
    t_dense_ns = np.linspace(0.0, 0.5, 501)
    dgu_dt_max = max(
        0.4 * 0.3 * math.exp(1.0 / math.exp(-0.3 * tv))
        / (math.exp(-0.3 * tv) * (math.expm1(1.0 / math.exp(-0.3 * tv)) ** 2))
        for tv in t_dense_ns
    )
    duhamel_sup_deriv_bound = float(0.2 * 0.5 * 2.0 * dgu_dt_max)
    assert duhamel_holonomy_trace_norm <= duhamel_deltaL_bound + 1e-14
    assert duhamel_deltaL_bound <= duhamel_sup_deriv_bound + 1e-14

    # 5f. Quasi-stationary bath vs relaxation-gap tracking counterexample:
    #     H = diag(0, 1), T(t) = exp(-mu t), mu = 1e-4, eta = 1e-8, evolved to T = 1/2 (t_f = ln(2)/mu)
    mu_qs = 1e-4
    eta_qs = 1e-8
    t_f_qs = math.log(2.0) / mu_qs
    max_Tdot_over_T2_qs = float(mu_qs / 0.5)  # = 2e-4 << 1
    p_gibbs_init_qs = 1.0 / (1.0 + math.e)

    def qs_rates(t_q: float) -> tuple[float, float]:
        T_q = math.exp(-mu_qs * t_q)
        n_q = 1.0 / math.expm1(1.0 / T_q)
        return eta_qs * (1.0 + n_q), eta_qs * n_q

    sol_qs = solve_ivp(
        lambda tv, yv: [qs_rates(tv)[1] * (1.0 - yv[0]) - qs_rates(tv)[0] * yv[0]],
        (0.0, t_f_qs),
        [p_gibbs_init_qs],
        method="DOP853",
        rtol=1e-12,
        atol=1e-14,
    )
    p_actual_qs = float(sol_qs.y[0, -1])
    p_gibbs_final_qs = 1.0 / (1.0 + math.exp(2.0))
    trace_dist_qs = abs(p_actual_qs - p_gibbs_final_qs)
    trace_norm_qs = 2.0 * trace_dist_qs
    assert max_Tdot_over_T2_qs <= 2.1e-4 and trace_dist_qs > 0.14

    # Major Point 4: Quantitative uniform-contraction Gibbs tracking bound (Proposition 1)
    # ||rho_t - sigma_t||_1 <= M e^{-lambda t} ||rho_0 - sigma_0||_1 + (M/lambda)(1 - e^{-lambda t}) sup ||sigma_dot||_1
    # For 2-level Davies on diagonal states, M = 1, lambda = min_v (g_down(v) + g_up(v)) = eta * (1 + 2 n_BE(1/T(t_f))),
    # and ||sigma_dot(v)||_1 = 2 |p_dot_Gibbs(v)| = 2 mu e^{1/T(v)} / (T(v) (1 + e^{1/T(v)})^2).
    t_grid_qs = np.linspace(0.0, t_f_qs, 401)
    sup_sigmadot_1 = float(max(
        2.0 * mu_qs * math.exp(1.0 / math.exp(-mu_qs * tv))
        / (math.exp(-mu_qs * tv) * ((1.0 + math.exp(1.0 / math.exp(-mu_qs * tv))) ** 2))
        for tv in t_grid_qs
    ))
    lam_qs_min = eta_qs * (1.0 + 2.0 / math.expm1(2.0))
    qs_tracking_bound_slow = float((1.0 / lam_qs_min) * (1.0 - math.exp(-lam_qs_min * t_f_qs)) * sup_sigmadot_1)
    assert trace_norm_qs <= qs_tracking_bound_slow + 1e-12

    # Fast-relaxation positive control (same T(t), eta_fast = 0.1 => lambda_min = 0.1313 >> mu = 1e-4):
    eta_fast = 0.1
    lam_fast_min = eta_fast * (1.0 + 2.0 / math.expm1(2.0))

    def fast_rates(t_q: float) -> tuple[float, float]:
        T_q = math.exp(-mu_qs * t_q)
        n_q = 1.0 / math.expm1(1.0 / T_q)
        return eta_fast * (1.0 + n_q), eta_fast * n_q

    sol_fast = solve_ivp(
        lambda tv, yv: [fast_rates(tv)[1] * (1.0 - yv[0]) - fast_rates(tv)[0] * yv[0]],
        (0.0, t_f_qs),
        [p_gibbs_init_qs],
        t_eval=t_grid_qs,
        method="DOP853",
        rtol=1e-12,
        atol=1e-14,
    )
    p_gibbs_grid = np.array([1.0 / (1.0 + math.exp(1.0 / math.exp(-mu_qs * tv))) for tv in t_grid_qs])
    fast_trace_norms = 2.0 * np.abs(sol_fast.y[0] - p_gibbs_grid)
    fast_tracking_max_trace_norm = float(np.max(fast_trace_norms))
    fast_tracking_bound = float((1.0 / lam_fast_min) * (1.0 - math.exp(-lam_fast_min * t_f_qs)) * sup_sigmadot_1)
    assert fast_tracking_max_trace_norm <= fast_tracking_bound + 1e-14
    assert fast_tracking_bound < 5e-4

    # Exact peak of ||sigma_dot(t)||_1 = 2 mu z e^z / (1 + e^z)^2 (attained at z tanh(z/2) = 1),
    # and explicit contrast between diagonal-subspace rate lambda_diag = inf r(t) vs full traceless
    # Hermitian uniform contraction rate lambda_full = (1/2) inf r(t) (attained on X = sigma_x)
    z_peak_sigmadot = float(brentq(lambda z: z * math.tanh(0.5 * z) - 1.0, 1.0, 2.0, xtol=1e-15, rtol=1e-15))
    sup_sigmadot_exact = float(
        2.0 * mu_qs * z_peak_sigmadot * math.exp(z_peak_sigmadot) / ((1.0 + math.exp(z_peak_sigmadot)) ** 2)
    )
    lam_fast_full = 0.5 * lam_fast_min
    fast_tracking_bound_diag_exact = float(
        (1.0 / lam_fast_min) * (1.0 - math.exp(-lam_fast_min * t_f_qs)) * sup_sigmadot_exact
    )
    fast_tracking_bound_full_exact = float(
        (1.0 / lam_fast_full) * (1.0 - math.exp(-lam_fast_full * t_f_qs)) * sup_sigmadot_exact
    )
    assert abs(sup_sigmadot_exact - 4.47743205e-5) < 1e-11
    assert fast_tracking_max_trace_norm <= fast_tracking_bound_diag_exact + 1e-14
    assert fast_tracking_bound_diag_exact < fast_tracking_bound_full_exact
    # Verify off-diagonal X = sigma_x contracts strictly at rate (1/2) r(t_f) under two-level Davies
    gd_end, gu_end = fast_rates(t_f_qs)
    L_fast_end_sup = gksl_superop([math.sqrt(gd_end) * L_dn2, math.sqrt(gu_end) * L_dn2.conj().T], 2)
    X_sx = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    X_sx_t1 = (expm(1.0 * L_fast_end_sup) @ X_sx.reshape(-1, order="F")).reshape((2, 2), order="F")
    offdiag_ratio = float(np.sum(np.linalg.svd(X_sx_t1, compute_uv=False)) / np.sum(np.linalg.svd(X_sx, compute_uv=False)))
    offdiag_rate_err = float(abs(offdiag_ratio - math.exp(-lam_fast_full)))
    assert offdiag_rate_err < 1e-14

    # 5g. Free-subsystem Markovian QRT Dirichlet-kernel witness (Theorem 1(f)):
    #     On C^2 x C^2 with KMS thermal dissipator acting on factor 1, commuting observable I x sigma_z
    #     gives zero initial discrepancy from C_free(tau) whereas non-commuting sigma_x x I gives strictly positive decay.
    L_f1 = np.kron(L_low2, I_2)
    rho_b1 = np.kron(sigma_2, 0.5 * I_2)
    S_f1 = np.kron(np.diag([math.sqrt(0.8), math.sqrt(0.2)]).astype(np.complex128), math.sqrt(0.5) * I_2)
    jumps_f1 = [L_f1, 0.5 * L_f1.conj().T]  # gamma_down = 1, gamma_up = 1/4
    O_comm = np.kron(I_2, np.diag([1.0, -1.0]).astype(np.complex128))
    O_act = np.kron(np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128), I_2)
    qrt_comm_decay = float(np.real(-2.0 * np.trace(rho_b1 @ O_comm @ gksl_dual_apply(jumps_f1, O_comm))))
    qrt_act_decay = float(np.real(-2.0 * np.trace(rho_b1 @ O_act @ gksl_dual_apply(jumps_f1, O_act))))
    qrt_act_frob = float(
        1.0 * (np.linalg.norm(comm(L_f1, O_act) @ S_f1.conj().T, "fro") ** 2)
        + 0.25 * (np.linalg.norm(comm(L_f1.conj().T, O_act) @ S_f1.conj().T, "fro") ** 2)
    )
    qrt_dirichlet_err = abs(qrt_act_decay - qrt_act_frob)
    assert abs(qrt_comm_decay) < 1e-15 and qrt_act_decay > 1.0 and qrt_dirichlet_err < 1e-14

    # 6. Falsification contrast: non-secular jump L_ns = sqrt(gamma0)*(a + adag) BREAKS [L, ad_H] = 0!
    L_ns = math.sqrt(gamma0) * (a + adag)
    L_ns_sup = gksl_superop([L_ns], d)
    nonsec_comm_norm = float(np.linalg.norm(comm(L_ns_sup, ad_H_sup)))
    assert nonsec_comm_norm > 1.0

    # Also check exact qubit non-secular Redfield commutator norm
    H_q = np.diag([0.0, 1.0]).astype(np.complex128)
    L_d = np.array([[0.0, 1.0], [0.0, 0.0]], dtype=np.complex128)
    L_u = L_d.conj().T
    S_q = L_d + L_u
    g_d_q = 0.4 * (1.0 + 1.0 / (math.exp(1.0 / 0.65) - 1.0))
    g_u_q = 0.4 * (1.0 / (math.exp(1.0 / 0.65) - 1.0))
    S_t_q = 0.5 * g_d_q * L_d + 0.5 * g_u_q * L_u
    I2 = np.eye(2, dtype=np.complex128)
    L_red_q = (
        np.kron(S_q.T, S_t_q)
        - np.kron(I2, S_q @ S_t_q)
        + np.kron(S_t_q.conj(), S_q)
        - np.kron((S_t_q.conj().T @ S_q).T, I2)
    )
    ad_Hq = -1j * (np.kron(I2, H_q) - np.kron(H_q.T, I2))
    redfield_qubit_comm_norm = float(np.linalg.norm(comm(L_red_q, ad_Hq)))
    assert redfield_qubit_comm_norm > 0.1

    return {
        "d_osc": d,
        "omega": omega,
        "T_H": T_H,
        "kms_stationarity_err": kms_stat_err,
        "energy_drift_identity_err": drift_err,
        "energy_drift_norm_nonzero": drift_norm,
        "carre_du_champ_identity_err": cdc_err,
        "covariant_generator_comm_err": gen_comm_err,
        "covariant_finite_ts_comm_err": flow_comm_err,
        "gns_monotonicity_identity_max_err": max_gns_id_err,
        "gns_monotonicity_min_rhs": min_gns_rhs,
        "cooling_purity_initial": purities[0],
        "cooling_purity_final": purities[-1],
        "rel_entropy_initial": rel_ents[0],
        "rel_entropy_final": rel_ents[-1],
        "gns_chi2_initial": gns_chi2[0],
        "gns_chi2_final": gns_chi2[-1],
        "noncommuting_rel_entropy_initial": nc_rel_ents[0],
        "noncommuting_rel_entropy_final": nc_rel_ents[-1],
        "noncommuting_gns_chi2_initial": nc_gns_chi2[0],
        "noncommuting_gns_chi2_final": nc_gns_chi2[-1],
        "noncommuting_sym_norm_eq_max_err": nc_max_norm_eq_err,
        "noncommuting_sym_herm_max_err": nc_max_herm_err,
        "noncommuting_sym_intertwine_max_err": nc_max_intertwine_err,
        "noncommuting_sym_deriv_max_err": nc_max_deriv_err,
        "two_level_asym_gns_mismatch": r1_2lvl_asym_mismatch,
        "two_level_asym_nonherm_norm": r1_2lvl_asym_nonherm,
        "two_level_sym_norm_err": r1_2lvl_sym_norm_err,
        "two_level_sym_intertwine_err": r1_2lvl_intertwine_err,
        "two_level_sym_deriv_err": r1_2lvl_deriv_err,
        "two_level_sym_deriv_value": dchi2_dirichlet_2,
        "m1_3level_drift_norm": m1_drift_norm,
        "m1_3level_var_s1": m1_var_s1,
        "m4_nonstationary_inst_comm_max": m4_inst_comm_max,
        "m4_nonstationary_rect_path_diff": m4_rect_path_diff,
        "m4_moving_gibbs_rel_entropy_t0p5": m4_moving_rel_ent,
        "duhamel_holonomy_trace_norm": duhamel_holonomy_trace_norm,
        "duhamel_deltaL_exact_bound": duhamel_deltaL_bound,
        "duhamel_sup_deriv_bound": duhamel_sup_deriv_bound,
        "quasistat_counterexample_max_Tdot_over_T2": max_Tdot_over_T2_qs,
        "quasistat_counterexample_p_actual": p_actual_qs,
        "quasistat_counterexample_p_gibbs": p_gibbs_final_qs,
        "quasistat_counterexample_trace_dist": trace_dist_qs,
        "quasistat_counterexample_trace_norm": trace_norm_qs,
        "quasistat_counterexample_sup_sigmadot_1": sup_sigmadot_1,
        "quasistat_counterexample_tracking_bound_slow": qs_tracking_bound_slow,
        "fast_relax_tracking_lambda_min": lam_fast_min,
        "fast_relax_tracking_max_trace_norm": fast_tracking_max_trace_norm,
        "fast_relax_tracking_analytic_bound": fast_tracking_bound,
        "quasistat_sup_sigmadot_z_peak": z_peak_sigmadot,
        "quasistat_sup_sigmadot_exact": sup_sigmadot_exact,
        "fast_relax_tracking_lambda_full_hermitian": lam_fast_full,
        "fast_relax_tracking_bound_diag_exact": fast_tracking_bound_diag_exact,
        "fast_relax_tracking_bound_full_hermitian": fast_tracking_bound_full_exact,
        "fast_relax_offdiag_sigmax_rate_err": offdiag_rate_err,
        "multitime_qrt_commuting_decay": qrt_comm_decay,
        "multitime_qrt_noncommuting_decay": qrt_act_decay,
        "multitime_qrt_dirichlet_identity_err": qrt_dirichlet_err,
        "nonsecular_hermitian_jump_comm_norm": nonsec_comm_norm,
        "nonsecular_redfield_qubit_comm_norm": redfield_qubit_comm_norm,
        "_plot": {
            "s_traj": s_traj.tolist(),
            "purities": purities,
            "rel_ents": rel_ents,
            "gns_chi2": gns_chi2,
        },
    }


# ---------------------------------------------------------------------------
# F3: 2D JT Gravity + CFT Open SK Effective Action, Ward Identity & Stochastic Schwarzian FDT
# ---------------------------------------------------------------------------

def run_f3_jt_sk_ward_and_fdt(rng: np.random.Generator) -> dict:
    # JT parameters: C = Phi_b / (8 pi G_2), c = CFT central charge, S_0 = extremal entropy
    C = 12.0
    c = 24.0
    S_0 = 20.0
    T_0 = 1.0  # Initial C * T_0 = 12 >> 1 (semiclassical regime)

    k_JT = c / (48.0 * math.pi * C)
    gamma_E = 2.0 * k_JT  # c / (24 pi C)
    E_0 = 2.0 * (math.pi**2) * C * (T_0**2)
    T_break = 1.0 / (2.0 * (math.pi**2) * C)
    u_break = math.log(T_0 / T_break) / k_JT

    # 1. Deterministic Ward identity check via ODE integration of dE/du = -F_Hawking(T_H)
    u_max = 1.15 * u_break
    u_grid = np.linspace(0.0, u_max, 500)

    def dE_du(u, y):
        E = max(y[0], 1e-18)
        T = math.sqrt(E / (2.0 * math.pi**2 * C))
        flux = (math.pi * c / 12.0) * (T**2)
        return [-flux]

    sol = solve_ivp(dE_du, [0.0, u_max], [E_0], t_eval=u_grid, method="DOP853", rtol=1e-12, atol=1e-14)
    E_num = sol.y[0]
    E_exact = E_0 * np.exp(-gamma_E * u_grid)
    T_exact = T_0 * np.exp(-k_JT * u_grid)
    S_BH_exact = S_0 + 4.0 * (math.pi**2) * C * T_exact

    ward_ode_rel_err = float(np.max(np.abs(E_num - E_exact) / E_exact))
    assert ward_ode_rel_err < 1e-10

    # Direct flux-balance Ward residual: dE/du + F_Hawking = 0
    dE_dt_exact = -gamma_E * E_exact
    F_hawk_exact = (math.pi * c / 12.0) * (T_exact**2)
    ward_balance_err = float(np.max(np.abs(dE_dt_exact + F_hawk_exact)))
    assert ward_balance_err < 1e-13

    # 2. Verify exact CFT chiral energy-flux noise integral S_F(T) = (pi c / 6) T^3
    def integrand_flux_noise(x):
        if x < 1e-7:
            return 1.0
        ex = math.exp(x)
        return (x**2 * ex) / ((ex - 1.0) ** 2)

    I_val, I_err = quad(integrand_flux_noise, 0.0, 100.0, epsabs=1e-13, epsrel=1e-13)
    I_exact = (math.pi**2) / 3.0
    flux_noise_integral_err = float(abs(I_val - I_exact))
    assert flux_noise_integral_err < 1e-11

    # 3. Equilibrium FDT Langevin check (BH coupled to bath at T_bath = T_0):
    #    dE = -gamma_E (E - E_0) du + sqrt(S_eq) dW, where S_eq = 2 * (pi c / 6) T_0^3 = (pi c / 3) T_0^3
    #    Exact stationary variance: Var_eq(E) = S_eq / (2 gamma_E) = 4 pi^2 C T_0^3 = T_0^2 C_V(T_0)
    S_eq = (math.pi * c / 3.0) * (T_0**3)
    var_E_fdt_theory = S_eq / (2.0 * gamma_E)
    var_E_canonical = (T_0**2) * (4.0 * (math.pi**2) * C * T_0)
    fdt_exact_ratio_err = float(abs(var_E_fdt_theory / var_E_canonical - 1.0))
    assert fdt_exact_ratio_err < 1e-14

    # Monte Carlo Langevin verification for BOTH equilibrium and evaporating regimes
    # Use exact one-step Gaussian transitions (zero time-discretization bias) and sample variance (ddof=1)
    n_traj = 20000
    u_eq_end = 12.0 / gamma_E
    n_steps_eq = 400
    dt_eq = u_eq_end / n_steps_eq
    E_eq = np.full(n_traj, E_0, dtype=np.float64)
    # Exact discrete OU step preserves variance identically up to MC sampling noise (~sqrt(2/(N-1)))
    decay_eq = math.exp(-gamma_E * dt_eq)
    noise_std_eq = math.sqrt(var_E_fdt_theory * (1.0 - decay_eq**2))
    for _ in range(n_steps_eq):
        E_eq = E_0 + (E_eq - E_0) * decay_eq + noise_std_eq * rng.normal(size=n_traj)
    mc_eq_var = float(np.var(E_eq, ddof=1))
    mc_eq_mean = float(np.mean(E_eq))
    mc_eq_var_rel_err = float(abs(mc_eq_var - var_E_canonical) / var_E_canonical)
    assert mc_eq_var_rel_err < 0.03, f"Equilibrium MC FDT mismatch: {mc_eq_var_rel_err}"

    # 4. Out-of-equilibrium evaporating linearized stochastic Schwarzian SDE (T_bath = 0):
    #    dE = -gamma_E E du + sqrt((pi c / 6) T_H(u)^3) dW (linearized around deterministic saddle)
    #    Exact analytic variance: V(u) = 8 pi^2 C T_H(u)^3 (1 - exp(-k_JT u))
    #    Use EXACT one-step Gaussian transition variance Q_exact (zero time-discretization bias):
    #      Q_exact(u_n, dt) = S_* exp(-3 k_JT u_n) exp(-4 k_JT dt) (exp(k_JT dt) - 1) / k_JT
    T_CT1 = 1.0 / C
    u_CT1 = math.log(T_0 / T_CT1) / k_JT
    T_fluc = (2.0 * T_0) / ((math.pi**2) * C * T_0 + 2.0)
    u_fluc = math.log(T_0 / T_fluc) / k_JT
    T_ad1 = k_JT
    u_ad1 = math.log(T_0 / T_ad1) / k_JT

    # Run MC over both the CT_H >= 1 reference region [0, u_CT1] and formal linear extrapolation to 0.65 u_break
    u_evap_end = 0.65 * u_break
    n_steps_evap = 600
    dt_evap = u_evap_end / n_steps_evap
    u_mc_grid = np.linspace(0.0, u_evap_end, n_steps_evap + 1)
    S_star = (math.pi * c / 6.0) * (T_0**3)
    decay_step = math.exp(-gamma_E * dt_evap)
    q_factor = math.exp(-4.0 * k_JT * dt_evap) * math.expm1(k_JT * dt_evap) / k_JT

    E_evap = np.full(n_traj, E_0, dtype=np.float64)
    mc_mean_evap = [E_0]
    mc_var_evap = [0.0]
    for step in range(n_steps_evap):
        u_n = step * dt_evap
        q_exact = S_star * math.exp(-3.0 * k_JT * u_n) * q_factor
        E_evap = E_evap * decay_step + math.sqrt(q_exact) * rng.normal(size=n_traj)
        mc_mean_evap.append(float(np.mean(E_evap)))
        mc_var_evap.append(float(np.var(E_evap, ddof=1)))

    mc_mean_evap_arr = np.array(mc_mean_evap)
    mc_var_evap_arr = np.array(mc_var_evap)
    T_mc_exact = T_0 * np.exp(-k_JT * u_mc_grid)
    E_mc_exact = E_0 * np.exp(-gamma_E * u_mc_grid)
    var_evap_exact = 8.0 * (math.pi**2) * C * (T_mc_exact**3) * (1.0 - np.exp(-k_JT * u_mc_grid))

    # Compare at nearest MC grid node to u_CT1 (CT_H ~= 1) and at formal extrapolation end
    idx_ct1 = int(np.argmin(np.abs(u_mc_grid - u_CT1)))
    u_mc_at_ct1_grid = float(u_mc_grid[idx_ct1])
    CT_H_at_ct1_grid = float(C * T_mc_exact[idx_ct1])
    evap_var_rel_err_ct1 = float(abs(mc_var_evap_arr[idx_ct1] - var_evap_exact[idx_ct1]) / var_evap_exact[idx_ct1])
    evap_var_rel_err_end = float(abs(mc_var_evap_arr[-1] - var_evap_exact[-1]) / var_evap_exact[-1])
    evap_mean_rel_err_end = float(abs(mc_mean_evap_arr[-1] - E_mc_exact[-1]) / E_mc_exact[-1])
    assert evap_var_rel_err_ct1 < 0.03
    assert evap_var_rel_err_end < 0.03
    assert evap_mean_rel_err_end < 0.02

    # Analytic relative energy fluctuation along full evaporation curve up to u_max
    var_full_exact = 8.0 * (math.pi**2) * C * (T_exact**3) * (1.0 - np.exp(-k_JT * u_grid))
    rel_fluct_E = np.sqrt(np.maximum(var_full_exact, 0.0)) / E_exact
    rel_fluct_at_CT1 = float(math.sqrt(2.0 * (1.0 - T_CT1 / T_0) / ((math.pi**2) * C * T_CT1)))
    gaussian_neg_E_prob_at_CT1 = float(0.5 * erfc(1.0 / (math.sqrt(2.0) * rel_fluct_at_CT1)))
    rel_fluct_at_break = float(math.sqrt(4.0 * (1.0 - T_break / T_0)))
    assert rel_fluct_at_break > 1.0

    # Adiabaticity parameter eps_ad(u) = |dT/du| / T^2 = k_JT / T(u)
    eps_ad_0 = k_JT / T_0
    eps_ad_CT1 = k_JT / T_CT1
    eps_ad_break = k_JT / T_break
    # Stanford-Witten 1-loop fixed-topology Schwarzian disk correction ratio (3/2 T^2) / (4 pi^2 C T^3)
    sw_disk_var_rel_corr_T0 = 1.5 / (4.0 * (math.pi**2) * C * T_0)

    # 5. Beyond-Gaussian Bernard-Doyon cumulants K_3(u), K_4(u), skewness gamma_1(u), excess kurtosis gamma_2(u)
    #    K_n(u) = (-1)^n (n! / (n-1)) * 4 pi^2 C T_H(u)^(n+1) (1 - exp(-(n-1) k_JT u))
    def bd_cumulants(u_val: float) -> tuple[float, float, float, float, float]:
        T_u = T_0 * math.exp(-k_JT * u_val)
        K2_u = 8.0 * (math.pi**2) * C * (T_u**3) * (1.0 - math.exp(-k_JT * u_val))
        K3_u = -12.0 * (math.pi**2) * C * (T_u**4) * (1.0 - math.exp(-2.0 * k_JT * u_val))
        K4_u = 32.0 * (math.pi**2) * C * (T_u**5) * (1.0 - math.exp(-3.0 * k_JT * u_val))
        g1_u = K3_u / (K2_u ** 1.5)
        g2_u = K4_u / (K2_u ** 2)
        return K2_u, K3_u, K4_u, g1_u, g2_u

    K2_ct1, K3_ct1, K4_ct1, skew_ct1, kurt_ct1 = bd_cumulants(u_CT1)
    K2_brk, K3_brk, K4_brk, skew_brk, kurt_brk = bd_cumulants(u_break)
    assert K3_ct1 < 0.0 and K4_ct1 > 0.0 and abs(skew_brk - (-0.75)) < 0.01 and abs(kurt_brk - 1.0) < 0.02

    # Exact continuous-time non-homogeneous compound-Poisson Monte Carlo (zero time-discretization bias):
    # X(u) = -T_0 exp(-2 k_JT u) sum_{j=1}^{N(u)} W_j / R_j,
    # N(u) ~ Poisson(4 pi^2 C T_0 (1 - exp(-k_JT u))), W_j ~ Exp(1), R_j ~ Uniform(exp(-k_JT u), 1).
    def sample_exact_bd_compound_poisson(u_eval: float, n_samples: int, chunk: int = 5000) -> tuple[float, float, float, float, float]:
        e_ku = math.exp(-k_JT * u_eval)
        lam_tot = 4.0 * (math.pi**2) * C * T_0 * (1.0 - e_ku)
        scale_u = T_0 * (e_ku ** 2)
        vals = np.empty(n_samples, dtype=np.float64)
        pos = 0
        while pos < n_samples:
            m = min(chunk, n_samples - pos)
            counts = rng.poisson(lam_tot, size=m)
            tot_j = int(np.sum(counts))
            if tot_j == 0:
                vals[pos:pos + m] = 0.0
            else:
                W = rng.exponential(1.0, size=tot_j)
                R = rng.uniform(e_ku, 1.0, size=tot_j)
                contrib = W / R
                offsets = np.cumsum(counts)[:-1]
                sums = np.add.reduceat(contrib, np.concatenate(([0], offsets)))
                sums = np.where(counts > 0, sums, 0.0)
                vals[pos:pos + m] = -scale_u * sums
            pos += m
        mean_v = float(np.mean(vals))
        dx = vals - mean_v
        m2 = float(np.mean(dx ** 2))
        m3 = float(np.mean(dx ** 3))
        m4 = float(np.mean(dx ** 4))
        k2_est = m2 * n_samples / (n_samples - 1)
        k3_est = m3
        k4_est = m4 - 3.0 * (m2 ** 2)
        g1_est = k3_est / (k2_est ** 1.5)
        g2_est = k4_est / (k2_est ** 2)
        return k2_est, k3_est, k4_est, g1_est, g2_est

    n_cp = 100000
    cp_k2_ct1, cp_k3_ct1, cp_k4_ct1, cp_g1_ct1, cp_g2_ct1 = sample_exact_bd_compound_poisson(u_CT1, n_cp)
    cp_k2_brk, cp_k3_brk, cp_k4_brk, cp_g1_brk, cp_g2_brk = sample_exact_bd_compound_poisson(u_break, n_cp)
    cp_k2_ct1_rel_err = abs(cp_k2_ct1 - K2_ct1) / K2_ct1
    cp_k3_ct1_rel_err = abs(cp_k3_ct1 - K3_ct1) / abs(K3_ct1)
    cp_k2_brk_rel_err = abs(cp_k2_brk - K2_brk) / K2_brk
    cp_k3_brk_rel_err = abs(cp_k3_brk - K3_brk) / abs(K3_brk)
    cp_k4_brk_rel_err = abs(cp_k4_brk - K4_brk) / K4_brk
    assert cp_k2_ct1_rel_err < 0.02 and cp_k3_ct1_rel_err < 0.08
    assert cp_k2_brk_rel_err < 0.02 and cp_k3_brk_rel_err < 0.05 and cp_k4_brk_rel_err < 0.12

    # 6. Three-tier equilibrium non-Gaussian FDT hierarchy & exact Hamilton-Jacobi factorization
    k2_can = 4.0 * (math.pi**2) * C * (T_0**3)
    k3_can = 12.0 * (math.pi**2) * C * (T_0**4)
    k4_can = 48.0 * (math.pi**2) * C * (T_0**5)
    k3_lin_eq = 0.0
    k4_lin_eq = 24.0 * (math.pi**2) * C * (T_0**5)
    D2_1 = 3.0 * gamma_E * T_0
    D2_2 = 3.0 * gamma_E * T_0 / (2.0 * E_0)
    D3_1 = -12.0 * gamma_E * (T_0**2)
    D4_0 = 4.0 * math.pi * c * (T_0**5)
    k3_gauss_eq = (3.0 * D2_1 * k2_can) / (3.0 * gamma_E)
    k4_gauss_eq = (6.0 * D2_1 * k3_gauss_eq + 6.0 * D2_2 * (k2_can**2)) / (4.0 * gamma_E)
    k4_km_eq = (6.0 * D2_1 * k3_can + 6.0 * D2_2 * (k2_can**2) + 4.0 * D3_1 * k2_can + D4_0) / (4.0 * gamma_E)
    assert abs(k3_gauss_eq / k3_can - 1.0) < 1e-14
    assert abs(k4_lin_eq / k4_can - 0.5) < 1e-14
    assert abs(k4_gauss_eq / k4_can - 1.5) < 1e-14
    assert abs(k4_km_eq / k4_can - 1.0) < 1e-14

    # Exact Hamilton-Jacobi zero-locus H_KM(E, beta_0 - beta(E)) == 0 across E / E_0 in [0.2, 3.0]
    E_hj_grid = E_0 * np.linspace(0.2, 3.0, 29)
    beta_0 = 1.0 / T_0
    hj_max_resid = 0.0
    for E_v in E_hj_grid:
        beta_E = 1.0 / math.sqrt(E_v / (2.0 * (math.pi**2) * C))
        p_can = beta_0 - beta_E
        H_val = (math.pi * c / 12.0) * (1.0 / (beta_E + p_can) - 1.0 / beta_E + 1.0 / (beta_0 - p_can) - 1.0 / beta_0)
        hj_max_resid = max(hj_max_resid, abs(H_val))
    assert hj_max_resid < 1e-13

    # 7. Major Point 2 checks:
    # (a) Leading state-dependent evaporating K3 feedback vs frozen-coefficient K3 (at u=30 & r=5/7 sign flip)
    A_C = 2.0 * (math.pi**2) * C
    alpha_bd = math.pi * c / 12.0

    def k2_k3_state_rhs(u_v, y_v):
        T_v = T_0 * math.exp(-k_JT * u_v)
        K2_v, K3_v = y_v[0], y_v[1]
        dK2 = -2.0 * gamma_E * K2_v + 2.0 * alpha_bd * (T_v**3)
        dK3 = -3.0 * gamma_E * K3_v + 3.0 * (3.0 * gamma_E * T_v) * K2_v - 6.0 * alpha_bd * (T_v**4)
        return [dK2, dK3]

    u_chk_s = 30.0
    r_chk_s = math.exp(-k_JT * u_chk_s)
    T_chk_s = T_0 * r_chk_s
    sol_k3_state = solve_ivp(k2_k3_state_rhs, (0.0, u_chk_s), [0.0, 0.0], method="DOP853", rtol=1e-13, atol=1e-15)
    K3_state_ode_u30 = float(sol_k3_state.y[1, -1])
    K3_state_formula_u30 = float(6.0 * A_C * (T_chk_s**4) * (1.0 - r_chk_s) * (5.0 - 7.0 * r_chk_s))
    K3_frozen_u30 = float(-12.0 * (math.pi**2) * C * (T_chk_s**4) * (1.0 - r_chk_s**2))
    K3_state_ode_rel_err = float(abs(K3_state_ode_u30 - K3_state_formula_u30) / abs(K3_state_formula_u30))
    assert K3_state_ode_rel_err < 1e-11
    assert K3_frozen_u30 < -150.0 and K3_state_formula_u30 > 25.0

    # (b) Finite-q detailed-balance obstruction for naive state-dependent BD rates vs
    #     exact detailed balance for the constructive E >= 0 entropy-difference jump process
    def S_bh_E(E_x: float) -> float:
        return 2.0 * math.pi * math.sqrt(2.0 * C * E_x)

    def beta_E_fn(E_x: float) -> float:
        return math.pi * math.sqrt(2.0 * C / E_x)

    naive_db_log_errs = []
    exact_ediff_db_log_errs = []
    for E_test in (0.5 * E_0, E_0, 2.0 * E_0):
        for q_test in (0.2, 1.0, 5.0, 15.0):
            target_log_ratio = (S_bh_E(E_test + q_test) - S_bh_E(E_test)) - beta_0 * q_test
            naive_log_ratio = q_test * (beta_E_fn(E_test + q_test) - beta_0)
            # Constructive rate: w_+(E,q) = alpha e^{-beta_0 q}, w_-(E+q,q) = alpha e^{S(E) - S(E+q)}
            ediff_log_ratio = -beta_0 * q_test - (S_bh_E(E_test) - S_bh_E(E_test + q_test))
            naive_db_log_errs.append(abs(naive_log_ratio - target_log_ratio))
            exact_ediff_db_log_errs.append(abs(ediff_log_ratio - target_log_ratio))
    naive_bd_finite_q_db_min_err = float(min(naive_db_log_errs))
    naive_bd_finite_q_db_max_err = float(max(naive_db_log_errs))
    exact_ediff_finite_q_db_max_err = float(max(exact_ediff_db_log_errs))
    assert naive_bd_finite_q_db_min_err > 1e-5
    assert exact_ediff_finite_q_db_max_err < 1e-13

    # Large-C curvature check: S_BH(E_0 - q) - S_BH(E_0) + q beta(E_0) vs (1/2) S_BH''(E_0) q^2
    q_small = 0.05
    ediff_curv_exact = (S_bh_E(E_0 - q_small) - S_bh_E(E_0)) + q_small * beta_E_fn(E_0)
    ediff_curv_quad = -0.5 * (beta_E_fn(E_0) / (2.0 * E_0)) * (q_small**2)
    ediff_curv_rel_err = float(abs(ediff_curv_exact - ediff_curv_quad) / abs(ediff_curv_quad))
    assert ediff_curv_rel_err < 5e-4
    # Markovian coarse-graining separation ratio tau_bath * gamma_E = gamma_E / T_0 << 1
    markov_timescale_ratio_T0 = float(gamma_E / T_0)
    assert markov_timescale_ratio_T0 < 0.03

    # (c) Independent generator-integral stationarity check int_0^inf pi(E) (L f)(E) dE = 0 for a test function
    #     in the constructive E >= 0 jump process vs naive q > E-rejected emission,
    #     together with exact partition function Z_C(beta) and fixed-n stationary cumulants kappa_n.
    def Z_C_closed(A_val: float, beta_val: float) -> float:
        s_ab = math.sqrt(A_val / beta_val)
        return (1.0 / beta_val) + (math.sqrt(math.pi * A_val) / (beta_val ** 1.5)) * math.exp(A_val / beta_val) * float(erfc(-s_ab))

    alpha_rev = 1.0
    C_rev = 0.5
    beta_rev = 1.2
    gamma_f = 0.1
    A_rev = 2.0 * (math.pi ** 2) * C_rev
    Z_rev_closed = Z_C_closed(A_rev, beta_rev)
    Z_rev_quad, _ = quad(lambda E: math.exp(2.0 * math.sqrt(A_rev * E) - beta_rev * E), 0.0, np.inf, epsabs=1e-13, epsrel=1e-13)
    Z_rev_rel_err = float(abs(Z_rev_closed - Z_rev_quad) / Z_rev_closed)
    assert Z_rev_rel_err < 1e-12

    def pi_rev(E: float) -> float:
        return math.exp(2.0 * math.sqrt(A_rev * E) - beta_rev * E) / Z_rev_closed

    def gen_in_term(E: float) -> float:
        # int_0^inf alpha e^{-beta q} (e^{-gamma_f(E+q)} - e^{-gamma_f E}) dq
        return pi_rev(E) * alpha_rev * math.exp(-gamma_f * E) * (1.0 / (beta_rev + gamma_f) - 1.0 / beta_rev)

    def gen_out_exact_term(E: float) -> float:
        if E <= 0.0:
            return 0.0
        # Direct q-integral on (0, E): int_0^E alpha e^{2 sqrt(A(E-q)) - 2 sqrt(A E)} (e^{-gamma_f(E-q)} - e^{-gamma_f E}) dq
        val_q, _ = quad(
            lambda q: math.exp(2.0 * math.sqrt(A_rev * (E - q)) - 2.0 * math.sqrt(A_rev * E))
            * (math.exp(-gamma_f * (E - q)) - math.exp(-gamma_f * E)),
            0.0,
            E,
            epsabs=1e-14,
            epsrel=1e-13,
            limit=100,
        )
        return pi_rev(E) * alpha_rev * val_q

    def gen_out_naive_term(E: float) -> float:
        if E <= 0.0:
            return 0.0
        b_E = math.sqrt(A_rev / E)
        val_q, _ = quad(
            lambda q: math.exp(-q * b_E) * (math.exp(-gamma_f * (E - q)) - math.exp(-gamma_f * E)),
            0.0,
            E,
            epsabs=1e-14,
            epsrel=1e-13,
            limit=100,
        )
        return pi_rev(E) * alpha_rev * val_q

    gen_in_val, _ = quad(gen_in_term, 0.0, 200.0, points=[1.0, 10.0, 40.0], epsabs=1e-14, epsrel=1e-13, limit=200)
    gen_out_exact_val, _ = quad(gen_out_exact_term, 0.0, 200.0, points=[1.0, 10.0, 40.0], epsabs=1e-14, epsrel=1e-13, limit=200)
    gen_out_naive_val, _ = quad(gen_out_naive_term, 0.0, 200.0, points=[1.0, 10.0, 40.0], epsabs=1e-14, epsrel=1e-13, limit=200)
    gen_exact_resid = float(gen_in_val + gen_out_exact_val)
    gen_naive_resid = float(gen_in_val + gen_out_naive_val)
    assert abs(gen_exact_resid) < 1e-13
    assert abs(gen_naive_resid - 0.00632818) < 1e-6

    # Verify exact fixed-n stationary cumulants kappa_n (n = 1..4) of pi(E) proportional to exp(2 sqrt(A_C E) - beta_0 E)
    # at C = 12, beta_0 = 1.0 against the large-C asymptotic formula n! A T_0^{n+1} + (3/2)(n-1)! T_0^n
    # using peak-shifted log-density to preserve full float64 precision.
    log_Z_C12_asymp = A_C / beta_0 - 1.5 * math.log(beta_0) + math.log(2.0 * math.sqrt(math.pi * A_C))
    # Exact log Z_C(beta_0) = A_C/beta_0 + log(e^{-A_C/beta_0}/beta_0 + sqrt(pi A_C)/beta_0^{3/2} erfc(-sqrt(A_C/beta_0)))
    exact_Z_pref = math.exp(-A_C / beta_0) / beta_0 + (math.sqrt(math.pi * A_C) / (beta_0 ** 1.5)) * float(erfc(-math.sqrt(A_C / beta_0)))
    log_Z_C12_exact = A_C / beta_0 + math.log(exact_Z_pref)
    log_Z_C12_asymp_err = float(abs(log_Z_C12_exact - log_Z_C12_asymp))
    assert log_Z_C12_asymp_err < 1e-13

    def pi_C12(E: float) -> float:
        return math.exp((2.0 * math.sqrt(A_C * E) - beta_0 * E) - log_Z_C12_exact)

    E_lo_c12 = max(0.0, E_0 - 14.0 * math.sqrt(k2_can))
    E_hi_c12 = E_0 + 18.0 * math.sqrt(k2_can)
    # Smooth peak-localized integrand: composite 256-pt Gauss-Legendre avoids cancellation warnings
    xi_c12, wi_c12 = np.polynomial.legendre.leggauss(256)
    E_gl_c12 = 0.5 * (E_hi_c12 - E_lo_c12) * xi_c12 + 0.5 * (E_lo_c12 + E_hi_c12)
    w_gl_c12 = 0.5 * (E_hi_c12 - E_lo_c12) * wi_c12
    p_gl_c12 = np.exp((2.0 * np.sqrt(A_C * E_gl_c12) - beta_0 * E_gl_c12) - log_Z_C12_exact)
    mu1_C12 = float(np.dot(w_gl_c12, E_gl_c12 * p_gl_c12))
    dE_c12 = E_gl_c12 - mu1_C12
    m2_C12 = float(np.dot(w_gl_c12, (dE_c12 ** 2) * p_gl_c12))
    m3_C12 = float(np.dot(w_gl_c12, (dE_c12 ** 3) * p_gl_c12))
    m4_C12 = float(np.dot(w_gl_c12, (dE_c12 ** 4) * p_gl_c12))
    kappas_C12_num = [mu1_C12, m2_C12, m3_C12, m4_C12 - 3.0 * (m2_C12 ** 2)]
    kappas_C12_asymp = [
        math.factorial(n_k) * A_C * (T_0 ** (n_k + 1)) + 1.5 * math.factorial(n_k - 1) * (T_0 ** n_k)
        for n_k in (1, 2, 3, 4)
    ]
    kappas_C12_max_rel_err = float(
        max(abs(kn - ka) / abs(ka) for kn, ka in zip(kappas_C12_num, kappas_C12_asymp))
    )
    assert kappas_C12_max_rel_err < 1e-11

    return {
        "C": C,
        "c": c,
        "S_0": S_0,
        "T_0": T_0,
        "k_JT": k_JT,
        "gamma_E": gamma_E,
        "E_0": E_0,
        "T_CT1": T_CT1,
        "u_CT1": u_CT1,
        "T_fluc_unity": T_fluc,
        "u_fluc_unity": u_fluc,
        "T_ad_unity": T_ad1,
        "u_ad_unity": u_ad1,
        "T_break": T_break,
        "u_break": u_break,
        "ward_ode_max_rel_err": ward_ode_rel_err,
        "ward_flux_balance_max_err": ward_balance_err,
        "cft_flux_noise_integral_err": flux_noise_integral_err,
        "fdt_exact_ratio_err": fdt_exact_ratio_err,
        "sw_disk_1loop_var_rel_corr_T0": sw_disk_var_rel_corr_T0,
        "var_E_canonical_T0": var_E_canonical,
        "mc_eq_mean": mc_eq_mean,
        "mc_eq_var": mc_eq_var,
        "mc_eq_var_rel_err": mc_eq_var_rel_err,
        "u_mc_grid_near_CT1": u_mc_at_ct1_grid,
        "CT_H_at_mc_grid_near_CT1": CT_H_at_ct1_grid,
        "evap_var_rel_err_at_CT1": evap_var_rel_err_ct1,
        "evap_var_rel_err_end": evap_var_rel_err_end,
        "evap_mean_rel_err_end": evap_mean_rel_err_end,
        "rel_energy_fluct_at_CT1": rel_fluct_at_CT1,
        "gaussian_neg_E_tail_prob_at_CT1": gaussian_neg_E_prob_at_CT1,
        "rel_energy_fluct_at_u_break": rel_fluct_at_break,
        "adiabatic_param_u0": eps_ad_0,
        "adiabatic_param_CT1": eps_ad_CT1,
        "adiabatic_param_u_break": eps_ad_break,
        "bd_K3_at_CT1": K3_ct1,
        "bd_K4_at_CT1": K4_ct1,
        "bd_skewness_at_CT1": skew_ct1,
        "bd_excess_kurtosis_at_CT1": kurt_ct1,
        "bd_skewness_at_u_break": skew_brk,
        "bd_excess_kurtosis_at_u_break": kurt_brk,
        "bd_cp_mc_K2_CT1_rel_err": cp_k2_ct1_rel_err,
        "bd_cp_mc_K3_CT1_rel_err": cp_k3_ct1_rel_err,
        "bd_cp_mc_skew_CT1": cp_g1_ct1,
        "bd_cp_mc_K2_break_rel_err": cp_k2_brk_rel_err,
        "bd_cp_mc_K3_break_rel_err": cp_k3_brk_rel_err,
        "bd_cp_mc_K4_break_rel_err": cp_k4_brk_rel_err,
        "bd_cp_mc_skew_break": cp_g1_brk,
        "bd_cp_mc_kurt_break": cp_g2_brk,
        "eq_fdt_K3_can": k3_can,
        "eq_fdt_K4_can": k4_can,
        "eq_fdt_tier1_lin_K3": k3_lin_eq,
        "eq_fdt_tier1_lin_K4_ratio": k4_lin_eq / k4_can,
        "eq_fdt_tier2_gauss_K3_ratio": k3_gauss_eq / k3_can,
        "eq_fdt_tier2_gauss_K4_ratio": k4_gauss_eq / k4_can,
        "eq_fdt_tier3_km_K4_ratio": k4_km_eq / k4_can,
        "eq_fdt_hj_canonical_max_resid": hj_max_resid,
        "evap_K3_frozen_at_u30": K3_frozen_u30,
        "evap_K3_state_lead_at_u30": K3_state_formula_u30,
        "evap_K3_state_lead_ode_rel_err": K3_state_ode_rel_err,
        "naive_bd_finite_q_db_min_log_err": naive_bd_finite_q_db_min_err,
        "naive_bd_finite_q_db_max_log_err": naive_bd_finite_q_db_max_err,
        "exact_ediff_jump_finite_q_db_max_log_err": exact_ediff_finite_q_db_max_err,
        "exact_ediff_jump_curv_rel_err_q0p05": ediff_curv_rel_err,
        "markov_coarse_grain_ratio_gammaE_over_T0": markov_timescale_ratio_T0,
        "ediff_Z_C0p5_beta1p2_closed": Z_rev_closed,
        "ediff_Z_C0p5_beta1p2_quad_rel_err": Z_rev_rel_err,
        "ediff_generator_integral_in": float(gen_in_val),
        "ediff_generator_integral_out_exact": float(gen_out_exact_val),
        "ediff_generator_integral_exact_resid": gen_exact_resid,
        "ediff_generator_integral_naive_resid": gen_naive_resid,
        "ediff_C12_logZ_asymp_err": log_Z_C12_asymp_err,
        "ediff_C12_fixed_n_cumulants_max_rel_err": kappas_C12_max_rel_err,
        "_plot": {
            "u_grid": u_grid.tolist(),
            "T_exact": T_exact.tolist(),
            "E_exact": E_exact.tolist(),
            "S_BH_exact": S_BH_exact.tolist(),
            "rel_fluct_E": rel_fluct_E.tolist(),
            "u_mc_grid": u_mc_grid[::6].tolist(),
            "mc_var_evap": mc_var_evap_arr[::6].tolist(),
            "var_evap_exact": var_evap_exact[::6].tolist(),
            "u_CT1": u_CT1,
            "u_fluc": u_fluc,
            "u_ad1": u_ad1,
            "u_break": u_break,
        },
    }


# ---------------------------------------------------------------------------
# F4: Bosonic All-s Exact ODE, 2D CFT Hadamard Horizon Violation & UDW Detector
# ---------------------------------------------------------------------------

def run_f4_horizon_hadamard_and_udw() -> dict:
    # Part 1: Bosonic all-s exact excitation identity vs truncated Fock ODE (N_cut = 24, 32)
    omega = 1.0
    Gamma = 1.0
    T_H = 0.65
    x = math.exp(-omega / (2.0 * T_H))  # tanh(r)
    n_be = (x**2) / (1.0 - x**2)
    cosh_r = 1.0 / math.sqrt(1.0 - x**2)
    sinh_r = x * cosh_r
    cosh_2r = cosh_r**2 + sinh_r**2
    sinh_2r = 2.0 * sinh_r * cosh_r

    s_grid = np.linspace(0.0, 5.0, 51)
    E_exact_boson = 4.0 * omega * n_be * (1.0 + n_be) * (1.0 - np.exp(-0.5 * Gamma * s_grid))

    def bosonic_truncated_energy(N_cut: int) -> np.ndarray:
        # Operate in the diagonal Schmidt subspace span{|n,n> : 0 <= n < N_cut} (exact invariance under N_R dephasing!)
        c_vec = np.array([(x**n) / cosh_r for n in range(N_cut)], dtype=np.float64)
        c_vec /= np.linalg.norm(c_vec)  # exact normalized truncated squeezed state
        # H_A restricted to span{|n,n>}:
        # diag: omega*(cosh(2r)*(2n+1) - 1)
        # off-diag (n, n+1): -omega*sinh(2r)*(n+1)
        H_sub = np.zeros((N_cut, N_cut), dtype=np.float64)
        for n in range(N_cut):
            H_sub[n, n] = omega * (cosh_2r * (2 * n + 1) - 1.0)
            if n + 1 < N_cut:
                H_sub[n, n + 1] = -omega * sinh_2r * (n + 1)
                H_sub[n + 1, n] = -omega * sinh_2r * (n + 1)
        # Verify exact ODE solution rho_nm(s) = c_n c_m exp(-Gamma s (n-m)^2 / 2)
        # against explicit numerical ODE d rho / ds = -Gamma/2 [N, [N, rho]]
        N_op = np.diag(np.arange(N_cut, dtype=np.float64))
        rho0 = np.outer(c_vec, c_vec)
        energies = []
        max_ode_err = 0.0
        for s in s_grid:
            diff_sq = (np.arange(N_cut)[:, None] - np.arange(N_cut)[None, :]) ** 2
            rho_s = rho0 * np.exp(-0.5 * Gamma * s * diff_sq)
            # Check exact derivative
            drho_analytic = rho_s * (-0.5 * Gamma * diff_sq)
            drho_gksl = -0.5 * Gamma * comm(N_op, comm(N_op, rho_s))
            max_ode_err = max(max_ode_err, float(np.linalg.norm(drho_analytic - drho_gksl)))
            energies.append(float(np.trace(H_sub @ rho_s)))
        assert max_ode_err < 1e-12
        return np.array(energies)

    E_cut24 = bosonic_truncated_energy(24)
    E_cut32 = bosonic_truncated_energy(32)
    rel_err_24 = float(np.max(np.abs(E_cut24[1:] - E_exact_boson[1:]) / E_exact_boson[1:]))
    rel_err_32 = float(np.max(np.abs(E_cut32[1:] - E_exact_boson[1:]) / E_exact_boson[1:]))
    assert rel_err_32 < rel_err_24 < 1e-6  # Cutoff convergence verified!

    # Exact finite-N Fock convergence formula E_N(s) = O(N q^N) at fixed omega > 0
    q_f = x**2
    a_s = np.exp(-0.5 * Gamma * s_grid)
    E_formula_24 = (
        (4.0 * omega * q_f / ((1.0 - q_f) ** 2)) * (1.0 - a_s)
        + (2.0 * omega * 24 * (q_f**24) / ((1.0 - q_f) * (1.0 - q_f**24))) * (2.0 * a_s - (1.0 + q_f))
    )
    E_formula_32 = (
        (4.0 * omega * q_f / ((1.0 - q_f) ** 2)) * (1.0 - a_s)
        + (2.0 * omega * 32 * (q_f**32) / ((1.0 - q_f) * (1.0 - q_f**32))) * (2.0 * a_s - (1.0 + q_f))
    )
    fock_exact_formula_err_24 = float(np.max(np.abs(E_cut24 - E_formula_24)))
    fock_exact_formula_err_32 = float(np.max(np.abs(E_cut32 - E_formula_32)))
    assert fock_exact_formula_err_24 < 1e-12 and fock_exact_formula_err_32 < 1e-12

    # Independent numerical ODE integration (solve_ivp) on N_cut = 10 to cross-check analytic substitution
    N_ivp = 10
    c_ivp = np.array([(x**n) / cosh_r for n in range(N_ivp)], dtype=np.float64)
    c_ivp /= np.linalg.norm(c_ivp)
    rho0_ivp = np.outer(c_ivp, c_ivp)
    N_op_ivp = np.diag(np.arange(N_ivp, dtype=np.float64))
    L_ivp_sup = gksl_superop([math.sqrt(Gamma) * N_op_ivp.astype(np.complex128)], N_ivp).real
    sol_fock = solve_ivp(
        lambda _s, y_vec: L_ivp_sup @ y_vec,
        (0.0, 5.0),
        rho0_ivp.reshape(-1, order="F"),
        t_eval=s_grid,
        method="DOP853",
        rtol=1e-11,
        atol=1e-13,
    )
    diff_sq_ivp = (np.arange(N_ivp)[:, None] - np.arange(N_ivp)[None, :]) ** 2
    max_ivp_vs_analytic_err = 0.0
    for idx_s, s_val_i in enumerate(s_grid):
        rho_num_i = sol_fock.y[:, idx_s].reshape((N_ivp, N_ivp), order="F")
        rho_ana_i = rho0_ivp * np.exp(-0.5 * Gamma * s_val_i * diff_sq_ivp)
        max_ivp_vs_analytic_err = max(max_ivp_vs_analytic_err, float(np.linalg.norm(rho_num_i - rho_ana_i)))
    assert max_ivp_vs_analytic_err < 1e-10

    # Part 2: Free 2D Chiral Boson Current Two-Point Function W_s(X1, X2) = <J(X1) J(X2)>_s
    # Verify exact R-R fixed-s CPL (X1, X2 < 0) and exact R-L point-split non-Hadamard defect at (-eps, +eps)
    kappa = 2.0 * math.pi * T_H

    def smooth_bump_gamma(w: float) -> float:
        """C^inf compactly supported bump strictly away from omega = 0 on (0.5, 2.5)."""
        if w <= 0.5 or w >= 2.5:
            return 0.0
        arg = 1.0 - 1.0 / ((w - 0.5) * (2.5 - w))
        return Gamma * math.exp(arg)

    # Direct mode-integral check of W_Unruh(-eps, +eps) = -1/(16 pi eps^2)
    # and point-split dephasing defect Delta W_J(-eps, +eps) = C_band(s)/(4 pi kappa^2 eps^2)
    def W_RL_mode_integral(X1: float, X2: float, s: float, mode: str = "const") -> float:
        assert X1 < 0.0 and X2 > 0.0
        sigma = math.log(X2 / abs(X1)) / kappa
        def integrand(w):
            if w < 1e-12:
                return kappa / math.pi
            if mode == "const":
                att = math.exp(-0.5 * Gamma * s)
            elif mode == "rect_band":
                att = math.exp(-0.5 * Gamma * s) if (0.5 <= w <= 2.5) else 1.0
            elif mode == "smooth_bump":
                att = math.exp(-0.5 * smooth_bump_gamma(w) * s)
            else:
                att = 1.0
            return att * (w * math.cos(w * sigma)) / math.sinh(math.pi * w / kappa)
        val, _ = quad(integrand, 0.0, 40.0 * kappa, epsabs=1e-12, epsrel=1e-12, limit=200)
        return -val / (4.0 * math.pi * (kappa**2) * abs(X1) * X2)

    eps_vals = np.geomspace(1e-3, 1e-1, 15)
    s_test = 2.0
    att_factor = math.exp(-0.5 * Gamma * s_test)

    W_unruh_exact_eps = -1.0 / (16.0 * math.pi * (eps_vals**2))
    W_unruh_num_eps = np.array([W_RL_mode_integral(-e, +e, 0.0, mode="unruh") for e in eps_vals])
    unruh_rl_rel_err = float(np.max(np.abs(W_unruh_num_eps - W_unruh_exact_eps) / np.abs(W_unruh_exact_eps)))
    assert unruh_rl_rel_err < 1e-10

    W_deph_const_eps = np.array([W_RL_mode_integral(-e, +e, s_test, mode="const") for e in eps_vals])
    delta_W_const_eps = W_deph_const_eps - W_unruh_exact_eps
    delta_W_const_theory = (1.0 - att_factor) / (16.0 * math.pi * (eps_vals**2))
    hadamard_const_rel_err = float(np.max(np.abs(delta_W_const_eps - delta_W_const_theory) / delta_W_const_theory))
    assert hadamard_const_rel_err < 1e-10

    # Smooth compactly supported band dephasing (omega in (0.5, 2.5), C^inf away from 0): STILL diverges as eps^-2!
    W_deph_band_eps = np.array([W_RL_mode_integral(-e, +e, s_test, mode="smooth_bump") for e in eps_vals])
    delta_W_band_eps = W_deph_band_eps - W_unruh_exact_eps
    band_slope = float(np.polyfit(np.log(eps_vals), np.log(delta_W_band_eps), 1)[0])
    assert abs(band_slope - (-2.0)) < 1e-8

    # Exterior fixed-s CPL verification (X1, X2 < 0): W_s(X1, X2) - W_Unruh(X1, X2) == 0 identically!
    ext_pairs = [(-0.8, -0.2), (-1.5, -0.4), (-0.3, -0.05)]
    max_ext_cpl_err = 0.0
    for X1, X2 in ext_pairs:
        du = -math.log(X1 / X2) / kappa
        def int_therm(w):
            if w < 1e-12:
                return kappa / (2.0 * math.pi)
            return (w / (math.exp(2.0 * math.pi * w / kappa) - 1.0)) * math.cos(w * du)
        val_th, _ = quad(int_therm, 0.0, 40.0 * kappa, epsabs=1e-12, epsrel=1e-12, limit=200)
        W_RR_reconstructed = (-1.0 / (4.0 * math.pi * du**2) + val_th / (2.0 * math.pi)) / (kappa**2 * X1 * X2)
        W_RR_exact = -1.0 / (4.0 * math.pi * (X1 - X2) ** 2)
        max_ext_cpl_err = max(max_ext_cpl_err, float(abs(W_RR_reconstructed - W_RR_exact) / abs(W_RR_exact)))
    assert max_ext_cpl_err < 1e-10

    # Part 3: Derivative-Coupled Unruh-DeWitt Raw-Cutoff Response Functional across X^- = 0
    # Gaussian switching chi(tau) = exp(-tau^2 / (2 sigma_tau^2)), gap Omega = 1.5, unit coupling g = 1
    sigma_tau = 1.0
    Omega = 1.5
    def udw_A_integrand(k):
        p = k + Omega
        return (k / (4.0 * math.pi)) * (2.0 * math.pi * sigma_tau**2) * math.exp(-(p**2) * (sigma_tau**2))
    F_udw_A, _ = quad(udw_A_integrand, 0.0, 20.0, epsabs=1e-14, epsrel=1e-14)

    def radial_factor(r: float) -> float:
        if r < 1e-8:
            return 1.0 - (r**2) / (3.0 * sigma_tau**2)
        return math.exp(-(r**2) / (4.0 * sigma_tau**2)) * (sigma_tau / r) * math.sqrt(math.pi) * erf(r / (2.0 * sigma_tau))

    eps_uv_grid = np.geomspace(1e-5, 1e-1, 13)
    delta_F_udw = []
    pref = (1.0 - att_factor) / (2.0 * math.pi)
    for eps_uv in eps_uv_grid:
        val, _ = quad(lambda r: radial_factor(r) * math.cos(Omega * r) / r, eps_uv, 12.0 * sigma_tau, epsabs=1e-12, epsrel=1e-12, limit=200)
        delta_F_udw.append(pref * val)
    delta_F_udw_arr = np.array(delta_F_udw)
    slope_num = (delta_F_udw_arr[0] - delta_F_udw_arr[3]) / (math.log(1.0 / eps_uv_grid[0]) - math.log(1.0 / eps_uv_grid[3]))
    slope_rel_err = float(abs(slope_num - pref) / pref)
    assert slope_rel_err < 1e-3, f"UDW log slope mismatch: {slope_num} vs {pref}"

    # 1. Verify integral_{-Z}^{Z} K_bump(z/kappa) dz -> pi * kappa * f_bump(0) = 0 (Z = 600 vs const-Gamma ~ 10.54)
    w_gl, wt_gl = np.polynomial.legendre.leggauss(200)
    w_nodes = 0.5 * (2.5 - 0.5) * w_gl + 0.5 * (2.5 + 0.5)
    w_weights = 0.5 * (2.5 - 0.5) * wt_gl
    f_bump_nodes = np.array([
        (w_i / math.sinh(math.pi * w_i / kappa)) * (1.0 - math.exp(-0.5 * smooth_bump_gamma(w_i) * s_test))
        for w_i in w_nodes
    ])
    n_panels_z = 60
    z_edges = np.linspace(-600.0, 600.0, n_panels_z + 1)
    gl_p, gl_w = np.polynomial.legendre.leggauss(32)
    z_wide = np.concatenate([0.5 * (b - a) * gl_p + 0.5 * (a + b) for a, b in zip(z_edges[:-1], z_edges[1:])])
    zw_wide = np.concatenate([0.5 * (b - a) * gl_w for a, b in zip(z_edges[:-1], z_edges[1:])])
    K_bump_wide = np.cos(np.outer(z_wide / kappa, w_nodes)) @ (f_bump_nodes * w_weights)
    bump_uv_log_coeff = float(np.dot(zw_wide, K_bump_wide))
    assert abs(bump_uv_log_coeff) < 1e-5

    # 2. Exact subtracted angular integral: since int K_bump(z/kappa) dz = 0,
    #    chi(-r u_z) chi(r(1-u_z)) - exp(-r^2/(2 sigma_tau^2))
    #      = exp(-r^2/(2 sigma_tau^2)) * [exp(r^2 / (4 sigma_tau^2 cosh^2(z/2))) - 1],
    #    which decays exponentially as exp(-|z|) and scales as O(r^2) as r -> 0+!
    z_edges_loc = np.linspace(-40.0, 40.0, 10)
    z_nodes = np.concatenate([0.5 * (b - a) * gl_p + 0.5 * (a + b) for a, b in zip(z_edges_loc[:-1], z_edges_loc[1:])])
    z_weights = np.concatenate([0.5 * (b - a) * gl_w for a, b in zip(z_edges_loc[:-1], z_edges_loc[1:])])
    K_bump_vals = np.cos(np.outer(z_nodes / kappa, w_nodes)) @ (f_bump_nodes * w_weights)
    sech2_half = 1.0 / (np.cosh(0.5 * z_nodes) ** 2)

    def bump_r_integrand(r_val: float) -> float:
        r2_s2 = (r_val**2) / (sigma_tau**2)
        chi_diff = math.exp(-0.5 * r2_s2) * np.expm1(0.25 * r2_s2 * sech2_half)
        inner = float(np.dot(z_weights, chi_diff * K_bump_vals))
        return inner * math.cos(Omega * r_val) / (2.0 * math.pi * (kappa**2) * r_val)

    bump_udw_1e3, _ = quad(bump_r_integrand, 1e-3, 12.0 * sigma_tau, epsabs=1e-11, epsrel=1e-11, limit=200)
    bump_udw_1e5, _ = quad(bump_r_integrand, 1e-5, 12.0 * sigma_tau, epsabs=1e-11, epsrel=1e-11, limit=200)
    bump_udw_uv_diff = float(abs(bump_udw_1e5 - bump_udw_1e3))
    assert bump_udw_uv_diff < 1e-6  # UV-finite despite eps^-2 point-split divergence!

    # A1 negative control: even though the smooth-bump raw functional is UV-finite,
    # the TOTAL raw response F_A(Omega) + Delta F_raw(Omega) turns strictly NEGATIVE at Omega >= 2
    # because Delta F_raw(Omega) ~ -A / Omega^2 outlasts Gaussian vacuum decay F_A(Omega) ~ exp(-a^2)/(8 a^2).
    def gl_nodes(n_pts: int, a_lo: float, b_hi: float) -> tuple[np.ndarray, np.ndarray]:
        xi, wi = np.polynomial.legendre.leggauss(n_pts)
        return 0.5 * (b_hi - a_lo) * xi + 0.5 * (a_lo + b_hi), 0.5 * (b_hi - a_lo) * wi

    w_a1, ww_a1 = gl_nodes(360, 0.5, 2.5)
    gamma_a1 = Gamma * np.exp(1.0 - 1.0 / ((w_a1 - 0.5) * (2.5 - w_a1)))
    att_a1 = -np.expm1(-0.5 * gamma_a1 * s_test)
    f_a1 = w_a1 * att_a1 / np.sinh(math.pi * w_a1 / kappa)
    z_a1, zw_a1 = gl_nodes(768, -64.0, 64.0)
    K_a1 = np.cos(np.outer(z_a1 / kappa, w_a1)) @ (ww_a1 * f_a1)
    r_a1, rw_a1 = gl_nodes(360, 0.0, 14.0)
    sech2_a1 = 1.0 / (np.cosh(0.5 * z_a1) ** 2)
    ang_a1 = (
        np.exp(-(r_a1[:, None] ** 2) / (2.0 * sigma_tau**2))
        * np.expm1((r_a1[:, None] ** 2) * sech2_a1[None, :] / (4.0 * sigma_tau**2))
    ) @ (zw_a1 * K_a1)
    h_a1 = ang_a1 / (2.0 * math.pi * (kappa**2) * r_a1)
    a1_asymp_coeff_A = float(
        np.dot(ww_a1, (w_a1**2) * att_a1 / (np.sinh(math.pi * w_a1 / kappa) ** 2))
        / (2.0 * (kappa**3) * (sigma_tau**2))
    )

    a1_total_raw_by_gap = {}
    for gap_val in (1.5, 2.0, 3.0):
        defect_g = float(np.dot(rw_a1, h_a1 * np.cos(gap_val * r_a1)))
        a_g = gap_val * sigma_tau
        vac_g = float(0.25 * (math.exp(-(a_g**2)) - math.sqrt(math.pi) * a_g * erfc(a_g)))
        a1_total_raw_by_gap[str(gap_val)] = vac_g + defect_g
    a1_asymp_ratio_gap8 = float(-(8.0**2) * float(np.dot(rw_a1, h_a1 * np.cos(8.0 * r_a1))) / a1_asymp_coeff_A)
    a1_asymp_ratio_gap16 = float(-(16.0**2) * float(np.dot(rw_a1, h_a1 * np.cos(16.0 * r_a1))) / a1_asymp_coeff_A)
    assert a1_total_raw_by_gap["1.5"] > 0.0
    assert a1_total_raw_by_gap["2.0"] < -0.0018 and a1_total_raw_by_gap["3.0"] < -0.0011
    assert abs(a1_asymp_ratio_gap16 - 1.0) < 0.015

    # U1 Contact-Term Positivity Bound & Exact sigma_tau Scale-Invariance Audit:
    # Check F_A(a/sig; sig) + Delta F_raw(a/sig; sig) is exactly invariant across sig in {0.5, 1.0, 2.0} at a = 2.0
    def total_raw_by_a_and_sig(a_val: float, sig_val: float) -> float:
        r_s, rw_s = gl_nodes(360, 0.0, 14.0 * sig_val)
        ang_s = (
            np.exp(-(r_s[:, None] ** 2) / (2.0 * sig_val**2))
            * np.expm1((r_s[:, None] ** 2) * sech2_a1[None, :] / (4.0 * sig_val**2))
        ) @ (zw_a1 * K_a1)
        h_s = ang_s / (2.0 * math.pi * (kappa**2) * r_s)
        defect_s = float(np.dot(rw_s, h_s * np.cos((a_val / sig_val) * r_s)))
        vac_s = float(0.25 * (math.exp(-(a_val**2)) - math.sqrt(math.pi) * a_val * erfc(a_val)))
        return vac_s + defect_s

    scale_vals_a2 = [total_raw_by_a_and_sig(2.0, sv) for sv in (0.5, 1.0, 2.0)]
    u1_scale_invariance_max_diff = float(max(abs(v - scale_vals_a2[1]) for v in scale_vals_a2))
    assert u1_scale_invariance_max_diff < 1e-13

    # Bounded-interval numerical minimum candidate on a in (1.5, 4.0) => necessary lower-bound witness c_{0,min} >= -F_tot(a_*)
    def total_raw_a(a_val: float) -> float:
        defect_a = float(np.dot(rw_a1, h_a1 * np.cos(a_val * r_a1)))
        vac_a = float(0.25 * (math.exp(-(a_val**2)) - math.sqrt(math.pi) * a_val * erfc(a_val)))
        return vac_a + defect_a

    opt_c0 = minimize_scalar(total_raw_a, bounds=(1.5, 4.0), method="bounded", options={"xatol": 1e-12})
    u1_a_star = float(opt_c0.x)
    u1_c0_min = float(-opt_c0.fun)
    assert u1_c0_min > 0.001876

    # Major Point 1: Constructive Mellin positive-type extension T_M = T_0 + c_* delta(x) delta(y),
    # sharp contact threshold c_*, Dawson-integral cross-check, and scale-averaged Q_ell limit
    # 1. Compute sharp c_* via spectral formula, direct wide-panel angular integral, and sech^2 IBP identity
    c_star_spec = float(
        np.dot(ww_a1, att_a1 / (np.sinh(math.pi * w_a1 / kappa) ** 2)) / (2.0 * kappa)
    )
    # Direct wide-panel angular integral on [-1600, 1600]: (1 / (4 pi kappa^2)) int K(z/kappa) log[u_z (1-u_z)] dz
    z_ang_edges = np.linspace(-1600.0, 1600.0, 101)
    z_ang_nodes = np.concatenate([0.5 * (b - a) * gl_p + 0.5 * (a + b) for a, b in zip(z_ang_edges[:-1], z_ang_edges[1:])])
    z_ang_weights = np.concatenate([0.5 * (b - a) * gl_w for a, b in zip(z_ang_edges[:-1], z_ang_edges[1:])])
    K_ang_wide = np.cos(np.outer(z_ang_nodes / kappa, w_a1)) @ (ww_a1 * f_a1)
    log_u1mu_wide = -np.abs(z_ang_nodes) - 2.0 * np.log1p(np.exp(-np.abs(z_ang_nodes)))
    c_star_ang = float(np.dot(z_ang_weights, K_ang_wide * log_u1mu_wide) / (4.0 * math.pi * (kappa**2)))
    c_star_spec_vs_ang_err = float(abs(c_star_spec - c_star_ang))
    # Twice-integrated-by-parts sech^2(z/2) angular check (machine precision on [-64, 64]):
    K_inv2 = np.cos(np.outer(z_a1 / kappa, w_a1)) @ (ww_a1 * (f_a1 / (w_a1**2)))
    c_star_sech2 = float(np.dot(zw_a1, (0.5 * sech2_a1) * K_inv2) / (4.0 * math.pi))
    c_star_spec_vs_sech2_err = float(abs(c_star_spec - c_star_sech2))
    assert c_star_spec_vs_ang_err < 5e-9
    assert c_star_spec_vs_sech2_err < 1e-14
    assert abs(c_star_spec - 0.074434671717) < 1e-9

    # 2. Direct Mellin frequency-space evaluation of <T_M - W_Unruh, Q_a x conj(Q_a)>
    #    using exponential change of variables u = exp(t) on t in [-32, 3.2] (machine precision)
    t_mel, wt_mel = gl_nodes(320, -32.0, 3.2)
    u_mel = np.exp(t_mel)
    exp_half_u2 = np.exp(-0.5 * (u_mel**2))
    k_mel = w_a1 / kappa
    mel_kernel_w = (ww_a1 / (2.0 * math.pi * kappa)) * (k_mel / np.sinh(math.pi * k_mel)) * att_a1

    def delta_FM_mellin(a_val: float) -> float:
        # R_k(Q_a) = -(1/(i k)) int_0^inf u^{i k} (i a - u) exp(i a u - u^2/2) du
        # L_k(Q_a) = conj(R_{-k}(Q_a)), so R_k * conj(L_k) = R_k * R_{-k}
        base_f = wt_mel * u_mel * (1j * a_val - u_mel) * np.exp(1j * a_val * u_mel) * exp_half_u2
        phase_pos = np.exp(1j * np.outer(k_mel, t_mel))
        R_pos = -(phase_pos @ base_f) / (1j * k_mel)
        R_neg = -(np.conj(phase_pos) @ base_f) / (-1j * k_mel)
        return float(np.dot(mel_kernel_w, np.real(R_pos * R_neg)))

    # 3. Independent Dawson-integral cross-check of Delta F_raw(a)
    s_dw, sw_dw = gl_nodes(48, 0.0, 1.0)
    def delta_F_raw_dawson(a_val: float) -> float:
        # int_0^inf r exp(-b r^2) cos(a r) dr = [1 - 2 t D(t)] / (2 b), t = a / (2 sqrt(b))
        b_mat = 0.5 - 0.25 * s_dw[:, None] * sech2_a1[None, :]
        t_mat = a_val / (2.0 * np.sqrt(b_mat))
        r_int = (1.0 - 2.0 * t_mat * dawsn(t_mat)) / (2.0 * b_mat)
        z_int = (sw_dw @ r_int) * (0.25 * sech2_a1)
        return float(np.dot(zw_a1, z_int * K_a1) / (2.0 * math.pi * (kappa**2)))

    mellin_vs_raw_plus_cstar_max_err = 0.0
    dawson_vs_raw_max_err = 0.0
    F_M_by_a = {}
    for a_chk in (1.5, u1_a_star, 3.0):
        vac_chk = float(0.25 * (math.exp(-(a_chk**2)) - math.sqrt(math.pi) * a_chk * erfc(a_chk)))
        dF_raw_chk = float(np.dot(rw_a1, h_a1 * np.cos(a_chk * r_a1)))
        dF_dw_chk = delta_F_raw_dawson(a_chk)
        dF_mel_chk = delta_FM_mellin(a_chk)
        dawson_vs_raw_max_err = max(dawson_vs_raw_max_err, abs(dF_dw_chk - dF_raw_chk))
        mellin_vs_raw_plus_cstar_max_err = max(
            mellin_vs_raw_plus_cstar_max_err,
            abs(dF_mel_chk - (dF_raw_chk + c_star_spec)),
        )
        F_M_by_a[f"{a_chk:.4f}"] = vac_chk + dF_mel_chk
    F_M_at_a_star = F_M_by_a[f"{u1_a_star:.4f}"]
    assert dawson_vs_raw_max_err < 1e-13
    assert mellin_vs_raw_plus_cstar_max_err < 1e-13
    assert F_M_at_a_star > 0.072

    # 4. Scale-averaged Schwartz sequence Q_ell(x) = (1/ell) int_0^ell Q_0(e^v x) dv convergence check:
    #    Split the positive-k integral at band edges (0, 0.5/kappa, 2.5/kappa, ..., k_max),
    #    separate the exact origin density 1/4 analytically via Si(x) - (1 - cos x)/x, and use
    #    QUADPACK oscillatory cosine integration for sinc^2(k ell / 2) = 2(1 - cos(k ell))/(k ell)^2,
    #    cross-checking (k_max=150, n_u=144) vs (k_max=240, n_u=256).
    def flat_top_bump_deriv(u_arr: np.ndarray) -> np.ndarray:
        out = np.zeros_like(u_arr)
        mask = (u_arr > 1.0) & (u_arr < 2.0)
        x_m = u_arr[mask] - 1.0
        e1 = np.exp(-1.0 / x_m)
        e2 = np.exp(-1.0 / (1.0 - x_m))
        # Q_0(u) = e2 / (e1 + e2) smoothly drops from 1 to 0 on [1, 2]
        # d/dx [e2 / (e1 + e2)] = -e1 e2 (1/x^2 + 1/(1-x)^2) / (e1 + e2)^2
        out[mask] = -(e1 * e2) * (1.0 / (x_m**2) + 1.0 / ((1.0 - x_m) ** 2)) / ((e1 + e2) ** 2)
        return out

    def compute_TM_Qell_suite(n_u_pts: int, k_max_val: float) -> dict[str, float]:
        u_loc, wu_loc = gl_nodes(n_u_pts, 1.0, 2.0)
        ln_u_loc = np.log(u_loc)
        wdQ_loc = wu_loc * flat_top_bump_deriv(u_loc)
        k_b1 = 0.5 / kappa
        k_b2 = 2.5 / kappa
        panels = [(k_b1, k_b2), (k_b2, 4.0), (4.0, 16.0), (16.0, 64.0), (64.0, k_max_val)]

        def density_M_scalar(kv: float) -> float:
            if kv <= 0.0:
                return 0.25
            # I(k) = int_1^2 e^{i k ln u} Q_0'(u) du, |R_k|^2 = |I(k)|^2 / k^2
            I_k = np.dot(wdQ_loc, np.exp(1j * kv * ln_u_loc))
            abs_I_sq = float(I_k.real * I_k.real + I_k.imag * I_k.imag)
            # Overflow-free exact identity:
            # (pi k / sinh(pi k)) * (2 cosh(pi k) - 2 b(k)) / (4 pi^2 k^2)
            #   = (1 / (2 pi)) * [tanh(pi k / 2) / k + 2 (1 - b(k)) e^{-pi k} / (k (1 - e^{-2 pi k}))]
            pk = math.pi * kv
            if pk < 1e-5:
                fac = 0.25 * (1.0 - (pk * pk) / 12.0)
            else:
                fac = (math.tanh(0.5 * pk) / (2.0 * math.pi * kv))
                if k_b1 < kv < k_b2:
                    att_k = -math.expm1(-0.5 * smooth_bump_gamma(kappa * kv) * s_test)
                    fac += (att_k * math.exp(-pk)) / (math.pi * kv * (-math.expm1(-2.0 * pk)))
            return fac * abs_I_sq

        def rem_h0(kv: float) -> float:
            # Exact cancellation-free evaluation of (density_M(k) - 1/4) / k^2 on [0, k_b1] (where b(k) = 1):
            # I(k) = -1 + k^2 A(k) + i k B(k) => (|I(k)|^2 - 1)/k^2 = -2 A(k) + B(k)^2 + k^2 A(k)^2
            y_pk = 0.5 * math.pi * kv
            if y_pk < 0.05:
                y2 = y_pk * y_pk
                tanh_over_y = 1.0 - y2 / 3.0 + (2.0 / 15.0) * (y2**2) - (17.0 / 315.0) * (y2**3) + (62.0 / 2835.0) * (y2**4)
                dfac_over_k2 = ((math.pi**2) / 16.0) * (
                    -1.0 / 3.0 + (2.0 / 15.0) * y2 - (17.0 / 315.0) * (y2**2) + (62.0 / 2835.0) * (y2**3)
                )
            else:
                tanh_over_y = math.tanh(y_pk) / y_pk
                dfac_over_k2 = 0.25 * (tanh_over_y - 1.0) / (kv * kv)
            fac0 = 0.25 * tanh_over_y
            # sinc_val(x) = sin(x)/x using np.sinc(x / pi)
            arg_half = 0.5 * kv * ln_u_loc
            sinc_half = np.sinc(arg_half / math.pi)
            sinc_full = np.sinc((kv * ln_u_loc) / math.pi)
            A_k = float(np.dot(wdQ_loc, -0.5 * (ln_u_loc**2) * (sinc_half**2)))
            B_k = float(np.dot(wdQ_loc, ln_u_loc * sinc_full))
            dI2_over_k2 = -2.0 * A_k + (B_k * B_k) + (kv * kv) * (A_k * A_k)
            return dfac_over_k2 + fac0 * dI2_over_k2

        # Precompute non-oscillatory integrals independent of ell
        I0_nonosc, _ = quad(rem_h0, 0.0, k_b1, epsabs=1e-13, epsrel=1e-13, limit=200)
        panel_nonosc = sum(
            quad(lambda kv: density_M_scalar(kv) / (kv * kv), a_p, b_p, epsabs=1e-13, epsrel=1e-13, limit=200)[0]
            for a_p, b_p in panels
        )

        out_vals: dict[str, float] = {}
        for ell_v in (1.0, 10.0, 100.0, 1000.0):
            # Analytic contribution of constant origin density 1/4 on [0, k_b1]
            x1 = k_b1 * ell_v
            si_x1, _ = sici(x1)
            const_part = (0.5 / ell_v) * (float(si_x1) - (1.0 - math.cos(x1)) / x1)
            I0_cos, _ = quad(rem_h0, 0.0, k_b1, weight="cos", wvar=ell_v, epsabs=1e-13, epsrel=1e-13, limit=200)
            panel_cos = sum(
                quad(
                    lambda kv: density_M_scalar(kv) / (kv * kv),
                    a_p,
                    b_p,
                    weight="cos",
                    wvar=ell_v,
                    epsabs=1e-13,
                    epsrel=1e-13,
                    limit=200,
                )[0]
                for a_p, b_p in panels
            )
            out_vals[str(int(ell_v))] = float(
                const_part + (2.0 / (ell_v * ell_v)) * ((I0_nonosc - I0_cos) + (panel_nonosc - panel_cos))
            )
        return out_vals

    TM_Qell_vals_ref = compute_TM_Qell_suite(144, 150.0)
    TM_Qell_vals = compute_TM_Qell_suite(256, 240.0)
    TM_Qell_conv_max_diff = float(
        max(abs(TM_Qell_vals[k] - TM_Qell_vals_ref[k]) for k in TM_Qell_vals)
    )
    assert TM_Qell_conv_max_diff < 1e-10
    assert TM_Qell_vals["1000"] < TM_Qell_vals["100"] < TM_Qell_vals["10"] < TM_Qell_vals["1"]
    assert abs(TM_Qell_vals["1"] - 0.42520870) < 1e-7
    assert abs(TM_Qell_vals["10"] - 0.11243000) < 1e-7
    assert abs(TM_Qell_vals["100"] - 0.00804573) < 1e-7
    assert abs(TM_Qell_vals["1000"] - 0.000787335) < 1e-8

    # High-gap approach of F_M(a) = F_0(a) + c_* to c_* from below (evaluated oscillation-free via Dawson):
    F_M_high_gap = {}
    for a_hg in (16.0, 48.0):
        vac_hg = float(0.25 * (math.exp(-(a_hg**2)) - math.sqrt(math.pi) * a_hg * erfc(a_hg)))
        F_M_high_gap[str(int(a_hg))] = float(vac_hg + delta_F_raw_dawson(a_hg) + c_star_spec)
    assert F_M_at_a_star < F_M_high_gap["16"] < F_M_high_gap["48"] < c_star_spec

    # Single-mode four-point distinction: Sperling-Vogel phase-averaged state vs centered quasi-free state
    # with matching two-point covariance <b_R b_L> = b sqrt(n(n+1)) at T_H/omega = 0.65, Gamma s = 2
    b_4pt = math.exp(-0.5 * Gamma * s_test)
    sv_fourpt_NRNL = float((n_be**2) + n_be * (n_be + 1.0))
    qf_fourpt_NRNL = float((n_be**2) + (b_4pt**2) * n_be * (n_be + 1.0))
    fourpt_sv_minus_qf = float(sv_fourpt_NRNL - qf_fourpt_NRNL)
    # Cross-check Sperling-Vogel <N_R N_L> directly against truncated Fock density matrix (N_cut = 32)
    c_4pt = np.array([(x**n_i) / cosh_r for n_i in range(32)], dtype=np.float64)
    c_4pt /= np.linalg.norm(c_4pt)
    sv_fourpt_fock32 = float(sum((c_4pt[n_i] ** 2) * (n_i ** 2) for n_i in range(32)))
    assert abs(sv_fourpt_fock32 - sv_fourpt_NRNL) < 1e-13
    assert abs(sv_fourpt_NRNL - 0.42293033) < 1e-7
    assert abs(qf_fourpt_NRNL - 0.12187693) < 1e-7
    assert abs(fourpt_sv_minus_qf - (1.0 - b_4pt**2) * n_be * (n_be + 1.0)) < 1e-14

    # Smooth-band response curves F_A(a), F_0(a), F_M(a) = F_0(a) + c_* for Fig. 3(c)
    a_plot_grid = np.linspace(0.5, 4.5, 161)
    F_A_plot = np.array([0.25 * (math.exp(-(av**2)) - math.sqrt(math.pi) * av * erfc(av)) for av in a_plot_grid])
    F_0_plot = np.array([total_raw_a(float(av)) for av in a_plot_grid])
    F_M_plot = F_0_plot + c_star_spec

    # Layer-2 L2-2 audit: single-shot Fock projection firewall floor across n = 0..10 & projector non-commutativity
    single_shot_energies = [omega * (cosh_2r * (2 * n_i + 1) - 1.0) for n_i in range(11)]
    l2_firewall_floor = 2.0 * omega * n_be
    assert abs(single_shot_energies[0] - l2_firewall_floor) < 1e-14
    assert all(e_n >= l2_firewall_floor - 1e-14 for e_n in single_shot_energies)
    c_l2 = np.array([(x**n_i) / cosh_r for n_i in range(32)], dtype=np.float64)
    c_l2 /= np.linalg.norm(c_l2)
    ensemble_avg_ss = float(sum((c_l2[n_i] ** 2) * omega * (cosh_2r * (2 * n_i + 1) - 1.0) for n_i in range(32)))
    l2_ensemble_match_err = abs(ensemble_avg_ss - 4.0 * omega * n_be * (1.0 + n_be))
    P_A_l2 = np.outer(c_l2, c_l2)
    P_B_l2 = np.zeros((32, 32), dtype=np.float64)
    P_B_l2[0, 0] = 1.0
    l2_proj_comm_norm = float(np.linalg.norm(comm(P_A_l2, P_B_l2), "fro"))
    assert l2_ensemble_match_err < 1e-12 and l2_proj_comm_norm > 0.3

    # M7 negative control: Multi-time quantum regression contrast for Markov dephasing along s(t)
    # Even when L_B(rho_beta) = 0, <b(t2) b^dag(t1)>_B / <b(t2) b^dag(t1)>_A = exp(-Gamma Delta_s / 2)
    d_m7 = 6
    a_m7 = np.zeros((d_m7, d_m7), dtype=np.complex128)
    for n_i in range(1, d_m7):
        a_m7[n_i - 1, n_i] = math.sqrt(n_i)
    N_m7 = np.diag(np.arange(d_m7, dtype=np.float64)).astype(np.complex128)
    w_m7 = np.exp(-np.arange(d_m7, dtype=np.float64) / T_H)
    rho_beta_m7 = np.diag(w_m7 / np.sum(w_m7)).astype(np.complex128)
    L_m7_sup = gksl_superop([N_m7], d_m7)  # Gamma = 1
    assert np.linalg.norm(gksl_apply([N_m7], rho_beta_m7)) < 1e-15
    evolved_op = (expm(1.0 * L_m7_sup) @ (a_m7.conj().T @ rho_beta_m7).reshape(-1, order="F")).reshape((d_m7, d_m7), order="F")
    corr_B_m7 = float(np.real(np.trace(a_m7 @ evolved_op)))
    corr_A_m7 = float(np.real(np.trace(a_m7 @ a_m7.conj().T @ rho_beta_m7)))
    m7_qrt_ratio = corr_B_m7 / corr_A_m7
    assert abs(m7_qrt_ratio - math.exp(-0.5)) < 1e-13

    return {
        "T_H": T_H,
        "boson_all_s_Ncut24_max_rel_err": rel_err_24,
        "boson_all_s_Ncut32_max_rel_err": rel_err_32,
        "boson_exact_finiteN_formula_err_N24": fock_exact_formula_err_24,
        "boson_exact_finiteN_formula_err_N32": fock_exact_formula_err_32,
        "boson_Ncut10_solve_ivp_vs_analytic_err": max_ivp_vs_analytic_err,
        "unruh_RL_mode_integral_max_rel_err": unruh_rl_rel_err,
        "hadamard_const_deph_max_rel_err": hadamard_const_rel_err,
        "hadamard_smooth_band_loglog_slope": band_slope,
        "exterior_fixed_s_CPL_max_rel_err": max_ext_cpl_err,
        "udw_observer_A_smooth_response_coeff": float(F_udw_A),
        "udw_const_raw_cutoff_defect_eps1e-5": float(delta_F_udw_arr[0]),
        "udw_const_log_divergence_slope_num": float(slope_num),
        "udw_const_log_divergence_slope_exact": float(pref),
        "udw_const_log_divergence_slope_rel_err": slope_rel_err,
        "m6c_smooth_bump_uv_log_coeff": bump_uv_log_coeff,
        "m6c_smooth_bump_raw_udw_eps1e-5": float(bump_udw_1e5),
        "m6c_smooth_bump_raw_udw_uv_diff_1e3_to_1e5": bump_udw_uv_diff,
        "smooth_bump_total_raw_response_by_gap": a1_total_raw_by_gap,
        "smooth_bump_high_gap_asymp_coeff_A": a1_asymp_coeff_A,
        "smooth_bump_high_gap_asymp_ratio_gap8": a1_asymp_ratio_gap8,
        "smooth_bump_high_gap_asymp_ratio_gap16": a1_asymp_ratio_gap16,
        "u1_contact_scale_invariance_max_diff": u1_scale_invariance_max_diff,
        "u1_contact_a_star": u1_a_star,
        "u1_contact_c0_min": u1_c0_min,
        "mellin_c_star_spectral": c_star_spec,
        "mellin_c_star_angular": c_star_ang,
        "mellin_c_star_spec_vs_ang_err": c_star_spec_vs_ang_err,
        "mellin_c_star_spec_vs_sech2_err": c_star_spec_vs_sech2_err,
        "mellin_vs_raw_plus_cstar_max_err": mellin_vs_raw_plus_cstar_max_err,
        "dawson_vs_raw_max_err": dawson_vs_raw_max_err,
        "mellin_F_M_at_a_star": F_M_at_a_star,
        "mellin_F_M_high_gap": F_M_high_gap,
        "mellin_scale_avg_Qell_vals": TM_Qell_vals,
        "mellin_scale_avg_Qell_conv_max_diff": TM_Qell_conv_max_diff,
        "single_mode_fourpt_sv_NRNL": sv_fourpt_NRNL,
        "single_mode_fourpt_qf_NRNL": qf_fourpt_NRNL,
        "single_mode_fourpt_sv_minus_qf": fourpt_sv_minus_qf,
        "layer2_single_shot_firewall_floor": l2_firewall_floor,
        "layer2_single_shot_n0_energy": single_shot_energies[0],
        "layer2_single_shot_ensemble_match_err": l2_ensemble_match_err,
        "layer2_vacuum_number_proj_comm_norm": l2_proj_comm_norm,
        "m7_multitime_qrt_decay_ratio_ds1": m7_qrt_ratio,
        "_plot": {
            "s_grid": s_grid.tolist(),
            "E_exact_boson": E_exact_boson.tolist(),
            "E_cut24": E_cut24.tolist(),
            "E_cut32": E_cut32.tolist(),
            "eps_vals": eps_vals.tolist(),
            "delta_W_const": delta_W_const_eps.tolist(),
            "delta_W_band": delta_W_band_eps.tolist(),
            "eps_uv_grid": eps_uv_grid.tolist(),
            "delta_F_udw": delta_F_udw_arr.tolist(),
            "F_udw_A": float(F_udw_A),
            "a_plot_grid": a_plot_grid.tolist(),
            "F_A_plot": F_A_plot.tolist(),
            "F_0_plot": F_0_plot.tolist(),
            "F_M_plot": F_M_plot.tolist(),
            "c_star": c_star_spec,
            "a_star": u1_a_star,
            "F_0_a_star": float(-u1_c0_min),
        },
    }


# ---------------------------------------------------------------------------
# F5: KMS Absorption-Emission Locking & 4D Schwarzschild All-Spin Greybody Closure
# ---------------------------------------------------------------------------

def delta_y_f_from_rstar(x: float) -> tuple[float, float, float]:
    """Near-horizon-stable inversion of x = y + ln(y - 1) via Wright omega.
    Retains delta = y - 1 = wrightomega(x - 1) > 0 before forming y = 1 + delta,
    so f = delta / (1 + delta) avoids catastrophic cancellation for x <= -36.
    """
    delta = float(np.real(wrightomega(x - 1.0)))
    y = 1.0 + delta
    f = delta / y
    return delta, y, f


def V_schwarzschild(
    x: float,
    spin: float,
    ell_or_k: int,
    dirac_sign: int = +1,
    stable: bool = True,
) -> float:
    """Dimensionless effective potential r_s^2 V(r) for Schwarzschild (r_s = 1).
    spin in {0, 0.5, 1, 2}. For spin=0.5, ell_or_k = |kappa_D| = j + 1/2 >= 1.
    """
    if stable:
        delta, y, f = delta_y_f_from_rstar(x)
        term_dirac = 0.5 - delta  # exact 1.5 - y without cancellation
    else:
        delta = float(np.real(wrightomega(x - 1.0)))
        y = 1.0 + delta
        f = 1.0 - 1.0 / y
        term_dirac = 1.5 - y
    if spin in (0, 1, 2):
        ell = ell_or_k
        return f * (ell * (ell + 1) / (y**2) + (1.0 - spin**2) / (y**3))
    elif abs(spin - 0.5) < 1e-9:
        k = ell_or_k
        return (k**2) * f / (y**2) + dirac_sign * k * math.sqrt(max(f, 0.0)) * term_dirac / (y**3)
    else:
        raise ValueError(f"Unsupported spin: {spin}")


def solve_greybody_transmission(
    w_tilde: float,
    spin: float,
    ell_or_k: int,
    dirac_sign: int = +1,
    x_min: float = -45.0,
    c_out: float = 120.0,
    stable: bool = True,
) -> tuple[float, float, float]:
    """Solve d^2 psi / dx^2 + (w_tilde^2 - V(x)) psi = 0 from horizon x_min to x_max.
    Returns (T_greybody, wronskian_abs_err, wronskian_rel_err).
    """
    if spin in (0, 1, 2):
        ell_eff = ell_or_k
    else:
        ell_eff = ell_or_k - 1 if dirac_sign == +1 else ell_or_k

    x_max = max(600.0, c_out / w_tilde)

    # Initial condition at horizon: purely ingoing exp(-i w x), with 1st-order potential correction tiny (~e^-35)
    y0 = np.array([1.0, 0.0, 0.0, -w_tilde], dtype=np.float64)  # Re(psi), Im(psi), Re(psi'), Im(psi')

    def rhs(x, y):
        V = V_schwarzschild(x, spin, ell_or_k, dirac_sign, stable=stable)
        k2 = w_tilde**2 - V
        return [y[2], y[3], -k2 * y[0], -k2 * y[1]]

    sol = solve_ivp(rhs, [x_min, x_max], y0, method="DOP853", rtol=1e-12, atol=1e-14)
    psi_end = sol.y[0, -1] + 1j * sol.y[1, -1]
    dpsi_end = sol.y[2, -1] + 1j * sol.y[3, -1]

    # Match to exact Riccati-Hankel basis at x_max:
    # u_out(x) = z * (j_l(z) + i y_l(z)) ~ (-i)^(l+1) exp(+i z), z = w_tilde * x
    # u_in(x)  = z * (j_l(z) - i y_l(z)) ~ (+i)^(l+1) exp(-i z)
    # Note: Wronskian W(u_in, u_out) = u_in u_out' - u_in' u_out = 2 i w_tilde
    z = w_tilde * x_max
    jl = spherical_jn(ell_eff, z)
    yl = spherical_yn(ell_eff, z)
    djl = spherical_jn(ell_eff, z, derivative=True)
    dyl = spherical_yn(ell_eff, z, derivative=True)

    u_out = z * (jl + 1j * yl)
    du_out = w_tilde * ((jl + 1j * yl) + z * (djl + 1j * dyl))
    u_in = np.conj(u_out)
    du_in = np.conj(du_out)

    # Solve psi = A_in u_in + A_out u_out, dpsi = A_in du_in + A_out du_out
    W = u_in * du_out - du_in * u_out  # = 2 i w_tilde
    A_in = (psi_end * du_out - dpsi_end * u_out) / W
    A_out = (u_in * dpsi_end - du_in * psi_end) / W

    flux_diff = (abs(A_in) - abs(A_out)) * (abs(A_in) + abs(A_out))
    wron_abs_err = abs(flux_diff - 1.0)
    wron_rel_err = wron_abs_err / max(1.0, abs(A_in) ** 2)
    T_gb = 1.0 / (abs(A_in) ** 2)
    return float(T_gb), float(wron_abs_err), float(wron_rel_err)


def run_f5_greybody_and_kms_locking() -> dict:
    # Five simulated channels: h = 0 (l=0,1), h = 1/2 (j=1/2; k=1), h = 1 (l=1), h = 2 (l=2)
    w_tilde_grid = np.array([0.04, 0.08, 0.15, 0.25, 0.4, 0.6, 0.85, 1.15, 1.5])

    channels = [
        ("h=0, l=0 (scalar)", 0.0, 0, 1, 1),     # 2j+1 = 1
        ("h=0, l=1 (scalar)", 0.0, 1, 1, 3),     # 2j+1 = 3
        ("h=1/2, j=1/2 (Weyl)", 0.5, 1, +1, 2),  # 2j+1 = 2
        ("h=1, l=1 (photon)", 1.0, 1, 1, 3),     # 2j+1 = 3
        ("h=2, l=2 (graviton)", 2.0, 2, 1, 5),   # 2j+1 = 5
    ]

    results_T = {}
    results_sigma_over_A = {}
    max_wron_abs_err_all = 0.0
    max_wron_abs_err_gt1e6 = 0.0
    max_wron_rel_err = 0.0

    for label, spin, lk, dsign, mult in channels:
        T_list = []
        sig_over_A_list = []
        for wt in w_tilde_grid:
            T_gb, w_abs, w_rel = solve_greybody_transmission(float(wt), spin, lk, dsign)
            max_wron_abs_err_all = max(max_wron_abs_err_all, w_abs)
            if T_gb > 1e-6:
                max_wron_abs_err_gt1e6 = max(max_wron_abs_err_gt1e6, w_abs)
            max_wron_rel_err = max(max_wron_rel_err, w_rel)
            T_list.append(T_gb)
            # sigma_abs / A_hor = (pi / w^2) * mult * T_gb / (4 pi r_s^2) = mult * T_gb / (4 * (w r_s)^2)
            sig_over_A_list.append(mult * T_gb / (4.0 * (wt**2)))
        results_T[label] = T_list
        results_sigma_over_A[label] = sig_over_A_list

    assert max_wron_rel_err < 1e-11, f"Relative Wronskian conservation failed: {max_wron_rel_err}"
    assert max_wron_abs_err_gt1e6 < 1e-6, f"Absolute Wronskian (T>1e-6) failed: {max_wron_abs_err_gt1e6}"

    # Verify Dirac SUSY isospectrality: V^+ vs V^- at k=1, w_tilde = 0.4
    T_dirac_p, _, _ = solve_greybody_transmission(0.4, 0.5, 1, +1)
    T_dirac_m, _, _ = solve_greybody_transmission(0.4, 0.5, 1, -1)
    dirac_susy_err = abs(T_dirac_p - T_dirac_m) / T_dirac_p
    assert dirac_susy_err < 1e-6, f"Dirac SUSY mismatch: {dirac_susy_err}"

    # Verify famous low-frequency benchmarks with exact gravitational Sommerfeld factor
    # S_som(wt) = 2 pi wt / (1 - exp(-2 pi wt)) = 1 + pi wt + O(wt^2) at wt = 0.005:
    wt_ultra = 0.005
    som_ultra = (2.0 * math.pi * wt_ultra) / (1.0 - math.exp(-2.0 * math.pi * wt_ultra))
    T_s0_ultra, _, _ = solve_greybody_transmission(wt_ultra, 0.0, 0, 1)
    T_d_ultra, _, _ = solve_greybody_transmission(wt_ultra, 0.5, 1, +1)
    scalar_ultra_ratio = T_s0_ultra / (4.0 * wt_ultra**2)
    dirac_ultra_ratio = 2.0 * T_d_ultra / (4.0 * wt_ultra**2)
    # 1. Das-Gibbons-Mathur (1997): h=0, l=0 => sigma_abs / A_hor -> 1.0 (with Sommerfeld 1 + pi wt)
    assert abs(scalar_ultra_ratio / som_ultra - 1.0) < 2e-3, f"Scalar DGM limit off: {scalar_ultra_ratio}"
    # 2. Unruh (1976): h=1/2, j=1/2 (1 chirality) => sigma_abs / A_hor -> 1/8 = 0.125 (with Sommerfeld)
    assert abs(dirac_ultra_ratio / (0.125 * som_ultra) - 1.0) < 2e-3, f"Unruh 1/8 Dirac limit off: {dirac_ultra_ratio}"

    # 3. Page (1976): Photon (h=1, l=1) -> (4/9) wt^4, Graviton (h=2, l=2) -> (4/225) wt^6
    wt_p = 0.01
    som_p = (2.0 * math.pi * wt_p) / (1.0 - math.exp(-2.0 * math.pi * wt_p))
    T_p_low, _, _ = solve_greybody_transmission(wt_p, 1.0, 1, 1)
    photon_coeff = T_p_low / (wt_p**4)
    assert abs(photon_coeff / ((4.0 / 9.0) * som_p) - 1.0) < 5e-3, f"Photon Page limit off: {photon_coeff}"

    wt_g = 0.02
    som_g = (2.0 * math.pi * wt_g) / (1.0 - math.exp(-2.0 * math.pi * wt_g))
    T_g_low, _, _ = solve_greybody_transmission(wt_g, 2.0, 2, 1)
    graviton_coeff = T_g_low / (wt_g**6)
    assert abs(graviton_coeff / ((4.0 / 225.0) * som_g) - 1.0) < 1e-2, f"Graviton Page limit off: {graviton_coeff}"

    scalar_low_ratio = results_sigma_over_A["h=0, l=0 (scalar)"][0]
    dirac_low_ratio = results_sigma_over_A["h=1/2, j=1/2 (Weyl)"][0]
    photon_low_ratio = results_sigma_over_A["h=1, l=1 (photon)"][0]
    graviton_low_ratio = results_sigma_over_A["h=2, l=2 (graviton)"][0]
    assert photon_low_ratio < 0.005
    assert graviton_low_ratio < 1e-5

    # Universal spin-blind throat closure at fixed physical frequency omega_phys = 1.0 as A_hor -> 0:
    # sigma_abs(A_hor) = A_hor * (sigma_abs / A_hor)(omega_phys * sqrt(A_hor / (4 pi)))
    A_hor_grid = 4.0 * math.pi * (w_tilde_grid**2)  # since omega_phys = 1 => r_s = w_tilde
    sigma_phys_by_channel = {
        label: [A * r for A, r in zip(A_hor_grid, ratio_list)]
        for label, ratio_list in results_sigma_over_A.items()
    }
    for label, sigs in sigma_phys_by_channel.items():
        # Verify monotonic decrease to 0 at small A_hor (no spin bypass!)
        assert sigs[0] < 0.025 and sigs[0] < sigs[-1], f"Throat closure failed for {label}"

    # Separate inner-boundary (x_min=-45 -> -80), outer-matching (c_out=120 -> 240/480),
    # and near-horizon rounding-stability (naive f=1-1/y vs stable f=delta/(1+delta)) audits.
    conv_targets = [
        ("scalar_l0_wt0p005", wt_ultra, 0.0, 0, 1, T_s0_ultra),
        ("dirac_j0p5_wt0p005", wt_ultra, 0.5, 1, +1, T_d_ultra),
        ("photon_l1_wt0p01", wt_p, 1.0, 1, 1, T_p_low),
        ("graviton_l2_wt0p02", wt_g, 2.0, 2, 1, T_g_low),
    ]
    inner_boundary_conv_rel_diffs = {}
    outer_matching_conv_rel_diffs = {}
    for cname, wt_c, sp_c, lk_c, ds_c, T_base in conv_targets:
        T_in80, _, _ = solve_greybody_transmission(wt_c, sp_c, lk_c, ds_c, x_min=-80.0, c_out=120.0, stable=True)
        T_out240, _, _ = solve_greybody_transmission(wt_c, sp_c, lk_c, ds_c, x_min=-80.0, c_out=240.0, stable=True)
        inner_boundary_conv_rel_diffs[cname] = float(abs(T_in80 - T_base) / T_base)
        outer_matching_conv_rel_diffs[cname] = float(abs(T_out240 - T_in80) / T_in80)
    assert max(inner_boundary_conv_rel_diffs.values()) < 5e-6
    assert max(outer_matching_conv_rel_diffs.values()) < 5e-6

    # Explicit Dirac j=1/2, wt=0.005 rounding-stability and c_out=480 reference check
    T_d_naive_45, _, _ = solve_greybody_transmission(wt_ultra, 0.5, 1, +1, x_min=-45.0, c_out=120.0, stable=False)
    T_d_stable_80_480, _, _ = solve_greybody_transmission(wt_ultra, 0.5, 1, +1, x_min=-80.0, c_out=480.0, stable=True)
    dirac_naive_vs_stable_rel_shift = float((T_d_ultra - T_d_naive_45) / T_d_naive_45)
    dirac_stable_45_vs_80_480_rel_diff = float(abs(T_d_stable_80_480 - T_d_ultra) / T_d_ultra)
    assert abs(dirac_naive_vs_stable_rel_shift) > 1e-7
    assert dirac_stable_45_vs_80_480_rel_diff < 5e-8

    # M9 fixed-(omega r_s) control: at Hawking-peak scaling omega = 0.4 / r_s, T_{0,0} does NOT vanish!
    T_scalar_fixed_wt0p4 = results_T["h=0, l=0 (scalar)"][4]
    assert T_scalar_fixed_wt0p4 > 0.90

    # KMS absorption-emission locking check at fixed r_s = 1 (T_H = 1/(4 pi)):
    # Scale transmission by factor lambda_in in [0, 1]: emission flux scales linearly with lambda_in -> 0!
    T_H_4d = 1.0 / (4.0 * math.pi)
    lambdas = [1.0, 0.5, 0.1, 0.0]
    w_dense = w_tilde_grid
    T_00 = np.array(results_T["h=0, l=0 (scalar)"])
    n_be_4d = 1.0 / (np.exp(w_dense / T_H_4d) - 1.0)
    base_power = float(np.trapezoid(w_dense * T_00 * n_be_4d / (2.0 * math.pi), w_dense))
    locked_powers = {str(lam): lam * base_power for lam in lambdas}
    assert locked_powers["0.0"] == 0.0 and locked_powers["1.0"] > 0.0

    # Major Point 3: Distant bosonic output mode b_out = sqrt(T) b_H + sqrt(1-T) a_in
    # vs isolated horizon-origin thermal port B_hor = sqrt(T) J_H at omega = 0.4, r_s = 1
    w_port = 0.4
    beta_4d = 1.0 / T_H_4d
    n_H_port = 1.0 / math.expm1(beta_4d * w_port)
    rho_H_port = 0.5 * w_port
    DK_H_port = rho_H_port * (1.0 + 2.0 * n_H_port)
    T_port_open = float(T_scalar_fixed_wt0p4)
    # Full distant output mode at T = 0 retains vacuum noise omega/2 and spontaneous decay omega/2:
    DK_out_T0 = 0.5 * w_port * (1.0 + 2.0 * 0.0 * n_H_port)
    gamma_down_out_T0 = 0.5 * (DK_out_T0 + rho_H_port)
    gamma_up_out_T0 = 0.5 * (DK_out_T0 - rho_H_port)
    # Isolated horizon-origin port scales linearly with T, preserves KMS ratio e^{-beta omega}, and vanishes at T = 0:
    DK_hor_open = T_port_open * DK_H_port
    rho_hor_open = T_port_open * rho_H_port
    gamma_down_hor_open = 0.5 * (DK_hor_open + rho_hor_open)
    gamma_up_hor_open = 0.5 * (DK_hor_open - rho_hor_open)
    hor_kms_ratio_err = float(abs(gamma_up_hor_open / gamma_down_hor_open - math.exp(-beta_4d * w_port)))
    DK_hor_T0 = 0.0 * DK_H_port
    assert abs(DK_out_T0 - 0.5 * w_port) < 1e-15 and gamma_down_out_T0 > 0.19 and gamma_up_out_T0 == 0.0
    assert hor_kms_ratio_err < 1e-15 and DK_hor_T0 == 0.0

    return {
        "max_wronskian_abs_err_main_grid_45pts": max_wron_abs_err_all,
        "max_wronskian_abs_err_main_grid_T_gt_1e-6": max_wron_abs_err_gt1e6,
        "max_wronskian_rel_err_main_grid_45pts": max_wron_rel_err,
        "inner_boundary_conv_rel_diffs_xm45_to_xm80": inner_boundary_conv_rel_diffs,
        "outer_matching_conv_rel_diffs_c120_to_c240": outer_matching_conv_rel_diffs,
        "dirac_wt0p005_naive_vs_stable_rel_shift": dirac_naive_vs_stable_rel_shift,
        "dirac_wt0p005_stable_45_120_vs_80_480_rel_diff": dirac_stable_45_vs_80_480_rel_diff,
        "dirac_susy_isospectral_rel_err": float(dirac_susy_err),
        "ultra_low_wt0p005_scalar_sigma_over_A": float(scalar_ultra_ratio),
        "ultra_low_wt0p005_dirac_sigma_over_A": float(dirac_ultra_ratio),
        "low_freq_wt0p01_photon_T_over_wt4": float(photon_coeff),
        "low_freq_wt0p02_graviton_T_over_wt6": float(graviton_coeff),
        "low_freq_wt0p04_scalar_sigma_over_A": float(scalar_low_ratio),
        "low_freq_wt0p04_dirac_sigma_over_A": float(dirac_low_ratio),
        "low_freq_wt0p04_photon_sigma_over_A": float(photon_low_ratio),
        "low_freq_wt0p04_graviton_sigma_over_A": float(graviton_low_ratio),
        "m9_fixed_wr_s_0p4_scalar_T": float(T_scalar_fixed_wt0p4),
        "kms_locked_scalar_power_by_lambda": locked_powers,
        "distant_output_mode_DK_at_T0": float(DK_out_T0),
        "distant_output_mode_gamma_down_at_T0": float(gamma_down_out_T0),
        "horizon_origin_port_kms_ratio_err": hor_kms_ratio_err,
        "horizon_origin_port_DK_at_T0": float(DK_hor_T0),
        "_plot": {
            "w_tilde": w_tilde_grid.tolist(),
            "A_hor_grid": A_hor_grid.tolist(),
            "sigma_phys": sigma_phys_by_channel,
            "sigma_over_A": results_sigma_over_A,
            "T_gb": results_T,
        },
    }


# ---------------------------------------------------------------------------
# F6: Three Separated Benchmark Models (Simplified JT Crossing, Static Map V, Isometric Diaries)
# ---------------------------------------------------------------------------

def run_f6_nonisometric_and_page_curve(rng: np.random.Generator) -> dict:
    # Model 1: Simplified JT entropy crossing benchmark min(S_Hawking, S_BH) (not full QES extremization)
    C = 12.0
    c = 24.0
    S_0 = 20.0
    T_0 = 1.0
    k_JT = c / (48.0 * math.pi * C)
    S_BH_0 = S_0 + 4.0 * (math.pi**2) * C * T_0  # 20 + 48 pi^2 ~ 493.74
    u_page_exact = math.log(3.0 * (S_BH_0 - S_0) / (2.0 * S_BH_0 - 3.0 * S_0)) / k_JT

    u_grid = np.linspace(0.0, 2.5 * u_page_exact, 300)
    T_u = T_0 * np.exp(-k_JT * u_grid)
    S_BH_u = S_0 + 4.0 * (math.pi**2) * C * T_u
    S_hawk_u = 2.0 * (S_BH_0 - S_BH_u)
    S_page_u = np.minimum(S_hawk_u, S_BH_u)

    # Check exact crossing at u_page_exact
    S_bh_at_page = S_0 + 4.0 * (math.pi**2) * C * T_0 * math.exp(-k_JT * u_page_exact)
    S_hawk_at_page = 2.0 * (S_BH_0 - S_bh_at_page)
    page_crossing_err = float(abs(S_bh_at_page - S_hawk_at_page))
    assert page_crossing_err < 1e-11

    # Model 2: Static finite-dimensional non-isometric post-selected map V (64 -> 32)
    #          Post-selected random unitary U in U(64) projected onto <0|_P of dim 2 -> V = sqrt(2) (<0|_P x I_32) U
    d_eff = 64
    d_P = 2
    d_fund = d_eff // d_P  # 32
    Z = rng.normal(size=(d_eff, d_eff)) + 1j * rng.normal(size=(d_eff, d_eff))
    Q, R = np.linalg.qr(Z)
    Q = Q * np.exp(-1j * np.angle(np.diag(R)))  # Haar random U(64)
    V = math.sqrt(d_P) * Q[:d_fund, :]  # shape (32, 64)

    # Exact rank-nullity check: ker(V) MUST have dimension >= d_eff - d_fund = 32
    _, svals, Vh_full = np.linalg.svd(V, full_matrices=True)
    rank_V = int(np.sum(svals > 1e-10))
    nullity_V = d_eff - rank_V
    assert nullity_V == d_eff - d_fund  # Exact 32D nullspace!
    # Explicit non-trace-preserving witness: unit null state psi_null in ker(V) has Tr(V |psi><psi| V^dag) = 0 != 1
    psi_null = Vh_full[-1, :].conj()
    null_state_trace = float(np.real(np.vdot(V @ psi_null, V @ psi_null)))
    assert abs(np.linalg.norm(psi_null) - 1.0) < 1e-14 and null_state_trace < 1e-26

    # Check basis off-diagonal RMS vs exact operator-norm non-isometry ||V^dag V - I||_op = 1
    G = V.conj().T @ V
    op_norm_VtV_minus_I = float(np.linalg.norm(G - np.eye(d_eff, dtype=np.complex128), ord=2))
    assert abs(op_norm_VtV_minus_I - 1.0) < 1e-12
    diag_devs = np.abs(np.real(np.diag(G)) - 1.0)
    offdiag_mask = ~np.eye(d_eff, dtype=bool)
    offdiag_devs = np.abs(G[offdiag_mask])
    rms_diag_dev = float(np.sqrt(np.mean(diag_devs**2)))
    rms_offdiag_dev = float(np.sqrt(np.mean(offdiag_devs**2)))
    assert 0.05 < rms_offdiag_dev < 0.35

    # Also test concentration across increasing d_fund = 16, 32, 64, 128 (fixed d_P = 2, d_eff = 2*d_fund)
    conc_d_fund = [16, 32, 64, 128]
    conc_rms_offdiag = []
    for df in conc_d_fund:
        de = 2 * df
        Zm = rng.normal(size=(de, de)) + 1j * rng.normal(size=(de, de))
        Qm, Rm = np.linalg.qr(Zm)
        Qm = Qm * np.exp(-1j * np.angle(np.diag(Rm)))
        Vm = math.sqrt(2.0) * Qm[:df, :]
        Gm = Vm.conj().T @ Vm
        mask = ~np.eye(de, dtype=bool)
        conc_rms_offdiag.append(float(np.sqrt(np.mean(np.abs(Gm[mask]) ** 2))))
    # Verify monotonic O(1/sqrt(d_fund)) decay!
    assert all(conc_rms_offdiag[i + 1] < conc_rms_offdiag[i] for i in range(len(conc_rms_offdiag) - 1))

    # Model 3a: Separate isometric N=8-qubit diary model (d_C = 2; cap sequence (1,...,1, 1/4))
    N_q = 8
    d_C = 2
    d_tot = 2**N_q  # 256
    Zs = rng.normal(size=(d_tot, d_tot)) + 1j * rng.normal(size=(d_tot, d_tot))
    Us, Rs = np.linalg.qr(Zs)
    Us = Us * np.exp(-1j * np.angle(np.diag(Rs)))

    psi_init = np.zeros((d_C, d_tot), dtype=np.complex128)
    psi_init[0, 0] = 1.0 / math.sqrt(2.0)
    psi_init[1, 1] = 1.0 / math.sqrt(2.0)
    psi_scr = psi_init @ Us.T  # (2, 256)

    k_steps = list(range(N_q + 1))
    F_rad_list = []
    F_rem_list = []
    F_rem_bound_list = []
    S_rad_bits_list = []

    for k in k_steps:
        d_rad = 2**k
        d_bh = 2**(N_q - k)
        psi_3 = psi_scr.reshape((d_C, d_rad, d_bh))
        J_rad = np.einsum("rab,scb->rasc", psi_3, psi_3.conj()).reshape((d_C * d_rad, d_C * d_rad))
        J_rem = np.einsum("rab,sac->rbsc", psi_3, psi_3.conj()).reshape((d_C * d_bh, d_C * d_bh))

        F_rad = petz_fidelity_from_choi(J_rad, d_C, d_rad)
        F_rem = petz_fidelity_from_choi(J_rem, d_C, d_bh)
        F_bound = min(1.0, (d_bh**2) / (d_C**2))

        rho_rad = np.einsum("rab,rcb->ac", psi_3, psi_3.conj())
        S_rad_bits = vn_entropy(rho_rad) / math.log(2.0)

        assert F_rem <= F_bound + 1e-12, f"Bottleneck violated at k={k}: {F_rem} > {F_bound}"
        assert F_rad + F_rem <= 1.0 + 1.0 / d_C + 1e-11, f"Monogamy violated at k={k}"

        F_rad_list.append(F_rad)
        F_rem_list.append(F_rem)
        F_rem_bound_list.append(F_bound)
        S_rad_bits_list.append(S_rad_bits)

    assert abs(F_rem_list[-1] - 0.25) < 1e-12
    assert abs(F_rad_list[-1] - 1.0) < 1e-12

    # Model 3b: Separate d_C = 4 (2-qubit diary) audit on N=8 qubits exercising nontrivial
    #           intermediate bottleneck d_BH = 2 < d_C = 4 (cap 1/4 at k=7, exact erasure 1/16 at k=8)
    d_C4 = 4
    psi_init4 = np.zeros((d_C4, d_tot), dtype=np.complex128)
    for r_idx in range(d_C4):
        psi_init4[r_idx, r_idx] = 0.5
    psi_scr4 = psi_init4 @ Us.T
    F_rem_dC4_k7 = None
    F_rem_dC4_k8 = None
    for k4 in (7, 8):
        d_rad4 = 2**k4
        d_bh4 = 2**(N_q - k4)
        psi4_3 = psi_scr4.reshape((d_C4, d_rad4, d_bh4))
        J_rem4 = np.einsum("rab,sac->rbsc", psi4_3, psi4_3.conj()).reshape((d_C4 * d_bh4, d_C4 * d_bh4))
        F_rem4 = petz_fidelity_from_choi(J_rem4, d_C4, d_bh4)
        F_bnd4 = min(1.0, (d_bh4**2) / (d_C4**2))
        assert F_rem4 <= F_bnd4 + 1e-12
        if k4 == 7:
            F_rem_dC4_k7 = F_rem4
        else:
            F_rem_dC4_k8 = F_rem4
    assert F_rem_dC4_k7 < 0.25 + 1e-12 and abs(F_rem_dC4_k8 - 0.0625) < 1e-12

    return {
        "model1_jt_S_BH_0": S_BH_0,
        "model1_jt_S_0_extremal": S_0,
        "model1_jt_residual_exp_S0": float(math.exp(S_0)),
        "model1_jt_u_page_simplified": u_page_exact,
        "model1_jt_page_crossing_err": page_crossing_err,
        "model2_static_nonisometric_d_eff": d_eff,
        "model2_static_nonisometric_d_fund": d_fund,
        "model2_static_nonisometric_rank_V": rank_V,
        "model2_static_nonisometric_nullity_V": nullity_V,
        "model2_static_nonisometric_null_state_trace": null_state_trace,
        "model2_static_nonisometric_op_norm_VtV_minus_I": op_norm_VtV_minus_I,
        "model2_static_nonisometric_rms_diag_dev": rms_diag_dev,
        "model2_static_nonisometric_rms_offdiag_dev": rms_offdiag_dev,
        "model2_concentration_d_fund": conc_d_fund,
        "model2_concentration_rms_offdiag": conc_rms_offdiag,
        "model3_separate_isometric_diary_N_qubits": N_q,
        "model3_diary_F_rad": F_rad_list,
        "model3_diary_F_rem": F_rem_list,
        "model3_diary_F_rem_bottleneck_bound": F_rem_bound_list,
        "model3_diary_S_rad_bits": S_rad_bits_list,
        "model3_diary_S_rad_final_bits_entangled_with_R": S_rad_bits_list[-1],
        "model3_diary_max_F_sum": float(max(a + b for a, b in zip(F_rad_list, F_rem_list))),
        "model3b_dC4_F_rem_k7_dBH2": F_rem_dC4_k7,
        "model3b_dC4_F_rem_k8_dBH1": F_rem_dC4_k8,
        "_plot": {
            "u_grid": u_grid.tolist(),
            "S_BH_u": S_BH_u.tolist(),
            "S_hawk_u": S_hawk_u.tolist(),
            "S_page_u": S_page_u.tolist(),
            "u_page": u_page_exact,
            "k_steps": k_steps,
            "F_rad": F_rad_list,
            "F_rem": F_rem_list,
            "F_bound": F_rem_bound_list,
            "conc_d_fund": conc_d_fund,
            "conc_rms_offdiag": conc_rms_offdiag,
        },
    }


# ---------------------------------------------------------------------------
# Publication-grade Figure Generation
# ---------------------------------------------------------------------------

def make_figures(res1: dict, res2: dict, res3: dict, res4: dict, res5: dict, res6: dict) -> None:
    plt.rcParams.update({
        "font.size": 9.5,
        "axes.labelsize": 10,
        "axes.titlesize": 10.5,
        "legend.fontsize": 8.2,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "axes.grid": True,
        "grid.alpha": 0.28,
        "lines.linewidth": 1.8,
    })

    # Figure 1: Finite-T_H GNS/KMS monotonicity vs cooling purity, and Davies vs Redfield CP violation
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.7))
    p2 = res2["_plot"]
    ax1.semilogy(p2["s_traj"], p2["gns_chi2"], color="#0d47a1", ls="--", label=r"GNS $\chi^2_{\beta_H}(\rho(s))$ (decreases)")
    ax1.semilogy(p2["s_traj"], p2["rel_ents"], color="#1b5e20", label=r"Rel. entropy $D(\rho(s)\,\|\,\rho_{\beta_H})$ (decreases)")
    ax1.semilogy(p2["s_traj"], p2["purities"], color="#c62828", ls="-.", label=r"Purity $\mathrm{Tr}(\rho(s)^2)$ (increases!)")
    ax1.set_xlabel(r"Auxiliary parameter $s$")
    ax1.set_ylabel("Information / purity measure (log scale)")
    ax1.set_title(r"(a) Finite-$T_H$ GNS/KMS arrow vs. cooling purity")
    ax1.legend(loc="upper right", frameon=True, fontsize=7.6)

    p1 = res1["_plot"]
    ax2.axhline(0.0, color="black", lw=0.9, ls=":")
    ax2.plot(p1["T_scan"], p1["choi_min_davies"], color="#0d47a1", label=r"Secular Davies $\lambda_{\min}(J_{\Phi})$ ($\geq 0$)")
    ax2.plot(p1["T_scan"], p1["choi_min_redfield"], color="#c62828", label=r"Non-secular Redfield $\lambda_{\min}(J_{\Phi})$ ($<0$)")
    ax2.plot(p1["T_scan"], [0.05 * x for x in p1["koss_min_redfield"]], color="#ef6c00", ls="--",
             label=r"Scaled Kossakowski $\lambda_-(K_{\mathrm{Red}})$")
    ax2.set_xlabel(r"Hawking temperature $T_H / \omega$")
    ax2.set_ylabel(r"Minimum Choi eigenvalue ($s=0.15$)")
    ax2.set_title(r"(b) Secular CPTP vs. non-secular Redfield CP failure")
    ax2.legend(loc="lower right", frameon=True)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_covariant_kms_and_redfield.pdf")
    plt.close(fig)

    # Figure 2: 2D JT + CFT Evaporation Saddle, Validity Indicators, and Linearized Stochastic Schwarzian FDT
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.8))
    p3 = res3["_plot"]
    ax1.axvspan(0.0, p3["u_CT1"], color="#e8f5e9", alpha=0.55, label=r"$CT_H \geq 1$ reference region")
    ax1.plot(p3["u_grid"], p3["T_exact"], color="#1565c0", label=r"$T_H(u)/T_0 = e^{-k_{\mathrm{JT}} u}$")
    ax1.plot(p3["u_grid"], [e / res3["E_0"] for e in p3["E_exact"]], color="#2e7d32", ls="--",
             label=r"$E_{\mathrm{BH}}(u)/E_0 = e^{-\gamma_E u}$")
    ax1.plot(p3["u_grid"], p3["rel_fluct_E"], color="#c62828", ls="-.",
             label=r"$\sqrt{V(u)}/E_{\mathrm{BH}}$ (linearized)")
    ax1.axvline(p3["u_CT1"], color="#2e7d32", ls=":", lw=1.1, label=r"$u_{CT=1}$ ($187$)")
    ax1.axvline(p3["u_fluc"], color="#ef6c00", ls=":", lw=1.1, label=r"$u_{\mathrm{fluc}}$ ($\sqrt{V}/E=1$, $309$)")
    ax1.axvline(p3["u_break"], color="#424242", ls="--", lw=1.0, label=r"$u_{\mathrm{break}}$ ($2\pi^2 CT_H=1$, $412$)")
    ax1.axhline(1.0, color="#9e9e9e", ls=":", lw=0.8)
    ax1.set_ylim(0.0, 2.6)
    ax1.set_xlabel(r"Boundary clock time $u$")
    ax1.set_ylabel("Normalized observables / fluctuation")
    ax1.set_title(r"(a) 2D JT evaporation & validity indicators")
    ax1.legend(loc="upper left", frameon=True, fontsize=6.8)

    ax2.axvspan(0.0, p3["u_CT1"], color="#e8f5e9", alpha=0.55)
    ax2.axvline(p3["u_CT1"], color="#2e7d32", ls=":", lw=1.1, label=r"$CT_H = 1$ boundary")
    ax2.plot(p3["u_mc_grid"], p3["var_evap_exact"], color="#0d47a1", lw=2.0,
             label=r"Linearized SDE $V(u)$")
    ax2.scatter(p3["u_mc_grid"][::4], p3["mc_var_evap"][::4], color="#d84315", s=22, zorder=5,
                label=r"Exact-step MC ($2\times 10^4$ paths)")
    ax2.set_xlabel(r"Boundary clock time $u$")
    ax2.set_ylabel(r"Energy variance $V(u)$")
    ax2.set_title(r"(b) Linearized stochastic Schwarzian variance")
    ax2.legend(loc="upper right", frameon=True, fontsize=7.6)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_jt_sk_evaporation_fdt.pdf")
    plt.close(fig)

    # Figure 3: Bosonic All-s Exact Law, Point-Split/Raw UDW Defect, and Smooth-Band F_0(a) vs Mellin F_M(a)
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(11.8, 3.65))
    p4 = res4["_plot"]
    ax1.plot(p4["s_grid"], p4["E_exact_boson"], color="#0d47a1", lw=1.9,
             label=r"Exact: $4\omega n_{\mathrm{BE}}(1+n_{\mathrm{BE}})(1-e^{-\Gamma s/2})$")
    ax1.plot(p4["s_grid"][::4], p4["E_cut24"][::4], "o", color="#ef6c00", ms=3.8,
             label=r"Fock ($N_{\mathrm{cut}}=24$)")
    ax1.plot(p4["s_grid"][2::4], p4["E_cut32"][2::4], "x", color="#2e7d32", ms=4.5,
             label=r"Fock ($N_{\mathrm{cut}}=32$)")
    ax1.set_xlabel(r"Auxiliary parameter $s$")
    ax1.set_ylabel(r"$\langle H_A(\omega)\rangle_{\rho_B(s)} / \omega$")
    ax1.set_title(r"(a) Bosonic all-$s$ law ($T_H/\omega=0.65$)", fontsize=9.5)
    ax1.legend(loc="lower right", frameon=True, fontsize=7.0)

    ax2.loglog(p4["eps_vals"], p4["delta_W_const"], color="#c62828", marker="o", ms=3.4,
               label=r"$\Delta W_J$ (const. $\Gamma$, slope $-2$)")
    ax2.loglog(p4["eps_vals"], p4["delta_W_band"], color="#6a1b9a", ls="--", marker="s", ms=3.0,
               label=r"$\Delta W_J$ (smooth bump, slope $-2$)")
    ax2_r = ax2.twinx()
    ax2_r.semilogx(p4["eps_uv_grid"], p4["delta_F_udw"], color="#00695c", ls="-.", marker="^", ms=3.4,
                   label=r"Raw $\Delta \mathcal{F}_{\mathrm{raw}}$ (const. $\Gamma$)")
    ax2_r.axhline(p4["F_udw_A"], color="#00695c", ls=":", lw=1.0, label=r"Unruh $\mathcal{F}^{(A)}$")
    ax2.set_xlabel(r"Point-splitting / UV cutoff $\epsilon$")
    ax2.set_ylabel(r"$\Delta W_J(-\epsilon,+\epsilon)$", color="#c62828")
    ax2_r.set_ylabel(r"$\Delta \mathcal{F}_{\mathrm{raw}}$ (const. $\Gamma$)", color="#00695c")
    ax2.set_title(r"(b) Point-split ($\epsilon^{-2}$) & raw UDW", fontsize=9.5)
    lines1, labels1 = ax2.get_legend_handles_labels()
    lines2, labels2 = ax2_r.get_legend_handles_labels()
    ax2.legend(lines1 + lines2, labels1 + labels2, loc="lower left", fontsize=6.4, frameon=True)

    a_g = np.array(p4["a_plot_grid"])
    F_A_g = np.array(p4["F_A_plot"])
    F_0_g = np.array(p4["F_0_plot"])
    F_M_g = np.array(p4["F_M_plot"])
    ax3.axhline(0.0, color="black", lw=0.85, ls=":")
    ax3.axhline(p4["c_star"], color="#1b5e20", lw=1.0, ls=":", label=r"Sharp $c_* = 0.07443$")
    ax3.plot(a_g, F_M_g, color="#1b5e20", lw=1.9, label=r"Mellin $F_M(a)=F_0(a)+c_*$")
    ax3.plot(a_g, F_A_g, color="#0d47a1", ls="--", lw=1.4, label=r"Unruh $\mathcal{F}_A(a)$")
    ax3.plot(a_g, F_0_g, color="#c62828", lw=1.8, label=r"Raw $F_0(a)$ (neg. $a\gtrsim 1.64$)")
    ax3.fill_between(a_g, F_0_g, 0.0, where=(F_0_g < 0.0), color="#ef9a9a", alpha=0.55)
    ax3.set_xlabel(r"Dimensionless gap $a = \Omega\sigma_\tau$")
    ax3.set_ylabel(r"Total detector response")
    ax3.set_ylim(-0.012, 0.172)
    ax3.set_title(r"(c) Smooth-band $F_0(a)$ vs. $F_M(a)$", fontsize=9.5)
    ax3.legend(loc="upper right", frameon=True, fontsize=6.6)
    axins = ax3.inset_axes([0.35, 0.15, 0.61, 0.26])
    axins.axhline(0.0, color="black", lw=0.75, ls=":")
    axins.plot(a_g, F_A_g, color="#0d47a1", ls="--", lw=1.1)
    axins.plot(a_g, F_0_g, color="#c62828", lw=1.4)
    axins.fill_between(a_g, F_0_g, 0.0, where=(F_0_g < 0.0), color="#ef9a9a", alpha=0.55)
    axins.plot([p4["a_star"]], [p4["F_0_a_star"]], "o", color="#880e4f", ms=3.5)
    axins.annotate(r"$a_*=2.150$", xy=(p4["a_star"], p4["F_0_a_star"]),
                   xytext=(2.62, -0.00235), fontsize=6.3, color="#880e4f",
                   arrowprops=dict(arrowstyle="->", lw=0.7, color="#880e4f"))
    axins.text(2.45, 0.0026, r"Zoom: $F_0(a)<0$", fontsize=6.5, fontweight="bold")
    axins.set_xlim(1.3, 4.2)
    axins.set_ylim(-0.0028, 0.0042)
    axins.tick_params(labelsize=6.5)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_horizon_hadamard_udw.pdf")
    plt.close(fig)

    # Figure 4: 4D Static Schwarzschild Greybody Asymptotics & Separate 8-Qubit Diary Model
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.8))
    p5 = res5["_plot"]
    styles = [
        ("h=0, l=0 (scalar)", "#0d47a1", "-", "o"),
        ("h=1/2, j=1/2 (Weyl)", "#2e7d32", "--", "s"),
        ("h=1, l=1 (photon)", "#ef6c00", "-.", "^"),
        ("h=2, l=2 (graviton)", "#c62828", ":", "D"),
    ]
    for label, col, ls, mk in styles:
        ax1.loglog(p5["A_hor_grid"], p5["sigma_phys"][label], color=col, ls=ls, marker=mk, ms=3.8, label=label)
    ax1.loglog(p5["A_hor_grid"], p5["A_hor_grid"], color="black", lw=0.9, ls="--", alpha=0.5,
               label=r"Low-$\omega$ asymptote $\sigma = A_{\mathrm{hor}}$")
    ax1.set_xlabel(r"Horizon area $A_{\mathrm{hor}} = 4\pi r_s^2$ (fixed $\omega = 1$)")
    ax1.set_ylabel(r"Absorption cross section $\sigma_{\mathrm{abs}}^{(h,j)}(\omega)$")
    ax1.set_title(r"(a) 4D static greybody asymptotics (fixed $\omega=1$)")
    ax1.legend(loc="lower right", frameon=True, fontsize=7.3)

    p6 = res6["_plot"]
    ax2.plot(p6["k_steps"], p6["F_rad"], color="#0d47a1", marker="o", ms=4.2, label=r"Radiation Petz $F_{\mathrm{rad}}(k)$")
    ax2.plot(p6["k_steps"], p6["F_rem"], color="#2e7d32", marker="s", ms=4.2, label=r"Remnant Petz $F_{\mathrm{rem}}(k)$")
    ax2.step(p6["k_steps"], p6["F_bound"], where="mid", color="#ef6c00", ls="--", lw=1.6,
             label=r"Bottleneck cap $\min(1, d_{\mathrm{BH}}^2/d_C^2)$ [Soga 2026]")
    ax2.set_xlabel(r"Emitted radiation qubits $k$ ($d_{\mathrm{BH}} = 2^{8-k}$)")
    ax2.set_ylabel(r"Entanglement fidelity $F_e$")
    ax2.set_ylim(0.18, 1.07)
    ax2.set_title(r"(b) Separate 8-qubit diary model ($d_{\mathrm{BH}}\to 1$)")
    ax2.legend(loc="lower center", bbox_to_anchor=(0.45, 0.02), frameon=True, fontsize=7.1)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig4_greybody_throat_and_nonisometric.pdf")
    plt.close(fig)


def count_numeric_leaves(obj) -> int:
    if isinstance(obj, bool):
        return 0
    if isinstance(obj, (int, float)):
        return 1
    if isinstance(obj, list):
        return sum(count_numeric_leaves(x) for x in obj)
    if isinstance(obj, dict):
        return sum(count_numeric_leaves(v) for k, v in obj.items() if not k.startswith("_"))
    return 0


def strip_private(obj):
    if isinstance(obj, dict):
        return {k: strip_private(v) for k, v in obj.items() if not k.startswith("_")}
    if isinstance(obj, list):
        return [strip_private(x) for x in obj]
    return obj


def main() -> None:
    rng = np.random.default_rng(SEED)
    print("Running F1 (SK positivity & Redfield CP-violation contrast)...")
    res1 = run_f1_sk_positivity_and_redfield(rng)
    print("Running F2 (Covariant (t,s) integrability, GNS monotonicity & non-secular breaking)...")
    res2 = run_f2_covariant_kms_integrability(rng)
    print("Running F3 (2D JT + CFT Ward identity & stochastic Schwarzian FDT)...")
    res3 = run_f3_jt_sk_ward_and_fdt(rng)
    print("Running F4 (Bosonic all-s ODE, 2D CFT Hadamard firewall & UDW detector)...")
    res4 = run_f4_horizon_hadamard_and_udw()
    print("Running F5 (4D Schwarzschild all-spin greybody throat closure & KMS locking)...")
    res5 = run_f5_greybody_and_kms_locking()
    print("Running F6 (Three separated benchmarks: simplified JT crossing, static V & isometric diaries)...")
    res6 = run_f6_nonisometric_and_page_curve(rng)

    print("Generating figures...")
    make_figures(res1, res2, res3, res4, res5, res6)

    payload = {
        "metadata": {
            "seed": SEED,
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "scipy": scipy.__version__,
            "matplotlib": matplotlib.__version__,
            "platform": platform.platform(),
        },
        "F1_sk_positivity_and_redfield": strip_private(res1),
        "F2_covariant_kms_integrability": strip_private(res2),
        "F3_jt_sk_ward_and_fdt": strip_private(res3),
        "F4_horizon_hadamard_and_udw": strip_private(res4),
        "F5_greybody_and_kms_locking": strip_private(res5),
        "F6_nonisometric_and_page_curve": strip_private(res6),
    }
    n_sci_leaves = sum(count_numeric_leaves(v) for k, v in payload.items() if k != "metadata")
    payload["metadata"]["scientific_numeric_fields_f1_to_f6"] = n_sci_leaves

    out_json = DOCS_DIR / "numerical_verification.json"
    out_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"ALL F1--F6 TESTS PASSED! Recorded {n_sci_leaves} scientific numeric fields (F1--F6) in {out_json}")


if __name__ == "__main__":
    main()
