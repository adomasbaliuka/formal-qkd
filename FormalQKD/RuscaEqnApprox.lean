/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import FormalQKD.RuscaEqn
public import Interval
public import Mathlib.Tactic.Basic

/-!
# Secret Key Length Equations (computable version!)

The secret key length is computed from parameters (both freely chosen by the protocol, as well as
properties of the hardware) and measurement results.

The file `RuscaEqn.lean` presents the equation in terms of `Real` numbers.
Those equations are useful for studying them and proving theorems about them.

This file allows **computing** the secret key length by rigorously approximating the `Real`-number
equations using interval arithmetic.

Compared to floating point computation, this makes sure that no rounding errors can happen and the
connection between the theory (`Real` numbers and proofs) and post-processing implementation
is rigorously ensured.

## Tags

QKD, secret, key, length, rate, quantum, key, distribution, post-processing

-/

@[expose] public section

/-!
### Definitions of minimum and maximum using interval arithmetic
-/

section MinMaxAbs

variable (α : Type) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (a b : α)

lemma min_eq_sum_sub_abs : min a b = 1/2 * (a + b) - 1/2 * abs (a - b) := by
  rw [abs_sub_comm]
  cancel_denoms
  linear_combination (max_add_min a b) - (max_sub_min_eq_abs a b)

lemma max_eq_sum_add_abs : max a b = 1/2 * (a + b) + 1/2 * abs (a - b) := by
  rw [abs_sub_comm]
  cancel_denoms
  linear_combination (max_add_min a b) + (max_sub_min_eq_abs a b)

end MinMaxAbs

namespace MyComputable

open Interval

/-- Clip a value within bounds a and b-/
local notation "M[" a ", " b "]{"c"}" => max a (min b c)

def Interval.max (a b : Interval) := 1/2 * (a + b) + 1/2 * abs (a - b)

instance instMaxInterval : Max Interval where
  max := Interval.max

def Interval.min (a b : Interval) := 1/2 * (a + b) - 1/2 * abs (a - b)

instance instMinInterval : Min Interval where
  min := Interval.min

@[approx] lemma mem_approx_min {a b : ℝ} {a' b' : Interval}
    (ha : approx a' a) (hb : approx b' b) :
    approx (Interval.min a' b') (min a b) := by
  rw [min_eq_sum_sub_abs, Interval.min]
  approx

@[approx] lemma mem_approx_max {a b : ℝ} {a' b' : Interval}
    (ha : approx a' a) (hb : approx b' b) :
    approx (Interval.max a' b') (max a b) := by
  rw [max_eq_sum_add_abs, Interval.max]
  approx

@[approx] lemma mem_approx_maxmin {n : ℕ} {a : ℝ} (a' : Interval) (ha : approx a' a) :
    approx (M[0, (n : Interval)]{a'}) (M[0, (n : ℝ)]{a}) := by
  apply mem_approx_max
  · simp
  · apply mem_approx_min
    · exact approx_natCast
    · assumption

@[approx] lemma mem_approx_maxmin' {n a : ℝ} {a' n' : Interval}
    (ha : approx a' a) (hn : approx n' n) :
    approx (M[0, n']{a'}) (M[0, (n : ℝ)]{a}) := by
  apply mem_approx_max
  · simp
  · apply mem_approx_min <;> assumption

instance : ToString Floating where
  toString f := f.toFloat.toString

instance instToStringInterval : ToString Interval where
  toString x := bif x = nan then "nan" else "[" ++ (toString x.lo) ++ "," ++ (toString  x.hi) ++ "]"

abbrev logb (b x : Interval) : Interval := log x / log b
abbrev log₂ (x : Interval) : Interval := logb 2 x

@[approx] lemma mem_approx_log₂ {x : Interval} {a : ℝ}
    (ax : approx x a) : approx (log₂ x) (Real.log₂ a) := by
  simp only [log₂, logb, Real.log₂, Real.logb]
  approx

/-!
### Auxilliary definitions (in terms of `Interval`)
-/

def binEntropy2 (p : Interval) := (-p * log p - (1 - p) * log (1 - p)) / log 2

/-- `binEntropy` is conservative -/
@[approx] lemma mem_approx_binEntropy {x : Interval} {a : ℝ}
    (ax : approx x a) : approx (binEntropy2 x) (Real.binEntropy2 a) := by
  simp only [binEntropy2, Real.binEntropy2, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_eq_neg]
  have : (-(a * Real.log a) + -((1 - a) * Real.log (1 - a))) =
    (-a * a.log - (1 - a) * (1 - a).log) := by ring
  rw [this]
  approx

def γ (a b c d : Interval) :=
    sqrt ((c + d) * (1 - b) * b / (c * d * log 2.) * log (
           (c + d) * (19 ^ 2) / (c * d * (1 - b) * b * (a * a))
       ) / (log 2.))

/-- `γ` is conservative -/
@[approx] lemma mem_approx_γ {ia ib ic id : Interval} {a b c d : ℝ}
    (ia_aprox : approx ia a)
    (ib_aprox : approx ib b)
    (ic_aprox : approx ic c)
    (id_aprox : approx id d) :
    approx (γ ia ib ic id) (Real.γ a b c d) := by
  rw [γ, Real.γ]
  approx

def δ (n ϵ : Interval) := sqrt (n * log (1 / ϵ) / 2)

@[approx] lemma mem_approx_δ {n' ε': Interval} {n ε : ℝ}
    (approxn : approx n' n)
    (approxε : approx ε' ε) :
    approx (δ n' ε') (Real.δ n ε) := by
  unfold Real.δ δ
  approx

-- τ(n, μ_1, P_μ1, μ_2, P_μ2) = (
--         (P_μ1 * exp -μ_1) * μ_1 ^ n / factorial(n)) +
--         (P_μ2 * exp -μ_2) * μ_2 ^ n / factorial(n))
--     )

def τ0 (par : ProtocolParams) : Interval :=
  ((par.P_μ1) * exp (- par.μ1) ) * 1  + (par.P_μ2 * exp (- par.μ2) ) * 1

@[approx] lemma mem_approx_τ0 (par : ProtocolParams) :
    approx (MyComputable.τ0 par) (ProtocolParams.τ0 par) := by
  simp only [ProtocolParams.τ0, MyComputable.τ0]
  approx

def τ1 (par : ProtocolParams) : Interval :=
  ((par.P_μ1) * exp (-par.μ1)) * (par.μ1) + (par.P_μ2 * exp (- par.μ2)) * par.μ2

@[approx] lemma mem_approx_τ1 (par : ProtocolParams) :
    approx (MyComputable.τ1 par) (ProtocolParams.τ1 par) := by
  simp only [ProtocolParams.τ1, MyComputable.τ1]
  approx

/-!
### Secret key length equations (in terms of `Interval`)
-/

section TakingProtocolParamsAndMeasResult

variable (par : ProtocolParams)
         (meas : MeasResult)

def n_Z_μ1_plus : Interval := exp par.μ1 / par.P_μ1 * (meas.n_Z_μ1 + δ (meas.n_Z) par.ε_1)

@[approx] lemma mem_approx_n_Z_μ1_plus :
    approx (n_Z_μ1_plus par meas) (Real.n_Z_μ1_plus par meas) := by
  simp only [Real.n_Z_μ1_plus, n_Z_μ1_plus]
  approx

def n_Z_μ1_minus : Interval := exp par.μ1 / par.P_μ1 * (meas.n_Z_μ1 - δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ1_minus :
    approx (n_Z_μ1_minus par meas) (Real.n_Z_μ1_minus par meas) := by
  simp only [Real.n_Z_μ1_minus, n_Z_μ1_minus]
  approx

def n_Z_μ2_plus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 + δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ2_plus :
    approx (n_Z_μ2_plus par meas) (Real.n_Z_μ2_plus par meas) := by
  simp only [Real.n_Z_μ2_plus, n_Z_μ2_plus]
  approx

def n_Z_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 - δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ2_minus :
    approx (n_Z_μ2_minus par meas) (Real.n_Z_μ2_minus par meas) := by
  simp only [Real.n_Z_μ2_minus, n_Z_μ2_minus]
  approx

def n_X_μ1_plus : Interval := exp par.μ1 / par.P_μ1 * (meas.n_X_μ1 + δ meas.n_X par.ε_1)

@[approx] lemma mem_approx_n_X_μ1_plus :
    approx (n_X_μ1_plus par meas) (Real.n_X_μ1_plus par meas) := by
  simp only [Real.n_X_μ1_plus, n_X_μ1_plus]
  approx

def n_X_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_X_μ2 - δ meas.n_X par.ε_1)

@[approx] lemma mem_approx_n_X_μ2_minus :
    approx (n_X_μ2_minus par meas) (Real.n_X_μ2_minus par meas) := by
  simp only [Real.n_X_μ2_minus, n_X_μ2_minus]
  approx

def m_X_μ1_plus : Interval := exp par.μ1 / par.P_μ1 * (meas.m_X_μ1 + δ meas.m_X par.ε_1)

@[approx] lemma mem_approx_m_X_μ1_plus :
    approx (m_X_μ1_plus par meas) (Real.m_X_μ1_plus par meas) := by
  simp only [Real.m_X_μ1_plus, m_X_μ1_plus]
  approx

def m_X_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.m_X_μ2 - δ meas.m_X par.ε_1)

@[approx] lemma mem_approx_m_X_μ2_minus :
    approx (m_X_μ2_minus par meas) (Real.m_X_μ2_minus par meas) := by
  simp only [Real.m_X_μ2_minus, m_X_μ2_minus]
  approx

def s_Z0_u : Interval := 2 *
  ((((τ0 par) * exp par.μ2) / par.P_μ2 * (meas.m_Z_μ2 + δ meas.m_Z par.ε_2)) + δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_s_Z0_u :
    approx (s_Z0_u par meas) (Real.s_Z0_u par meas) := by
  simp only [Real.s_Z0_u, s_Z0_u]
  approx

def s_X0_u : Interval :=
  let τ0 := τ0 par
  M[0, meas.n_X]{
    2 *
    (
        ((τ0 * exp par.μ2) / par.P_μ2 * (meas.m_X_μ2 + δ meas.m_X par.ε_2))
        + δ meas.n_X par.ε_1
    )
  }

@[approx] lemma mem_approx_s_X0_u :
    approx (s_X0_u par meas) (Real.s_X0_u par meas) := by
  simp only [Real.s_X0_u, s_X0_u]
  approx

def v_X1_u : Interval :=
  let m_X_μ1_plus := m_X_μ1_plus par meas
  let m_X_μ2_minus := m_X_μ2_minus par meas
  M[0, meas.n_X]{
    ((τ1 par) * (m_X_μ1_plus - m_X_μ2_minus) / (par.μ1 - par.μ2))
  }

@[approx] lemma mem_approx_v_X1_u : approx (v_X1_u par meas) (Real.v_X1_u par meas) := by
  simp only [Real.v_X1_u, v_X1_u]
  approx

def s_Z0_l : Interval :=
  let n_Z_μ2_minus := n_Z_μ2_minus par meas
  let n_Z_μ1_plus := n_Z_μ1_plus par meas
  M[0, meas.n_Z]{
    (τ0 par) / (par.μ1 - par.μ2) * (par.μ1 * n_Z_μ2_minus - par.μ2 * n_Z_μ1_plus)
  }

@[approx] lemma mem_approx_s_Z0_l : approx (s_Z0_l par meas) (Real.s_Z0_l par meas) := by
  simp only [Real.s_Z0_l, s_Z0_l]
  approx

def s_Z1_l : Interval :=
  let s_Z0_u := s_Z0_u par meas
  let n_Z_μ2_minus := n_Z_μ2_minus par meas
  let n_Z_μ1_plus := n_Z_μ1_plus par meas
  let μ1 := par.μ1
  let μ2 := par.μ2
  M[0, meas.n_Z]{
    ((τ1 par) * μ1 / (μ2 * (μ1 - μ2)))
        * (n_Z_μ2_minus - (μ2 ^ 2 / μ1 ^ 2)
        * n_Z_μ1_plus
        - ((μ1 ^ 2 - μ2 ^ 2) / (μ1 ^ 2) * (s_Z0_u / (τ0 par))))
  }

@[approx] lemma mem_approx_s_Z1_l : approx (s_Z1_l par meas) (Real.s_Z1_l par meas) := by
  simp only [Real.s_Z1_l, s_Z1_l]
  approx

def s_X1_l : Interval :=
  let n_X_μ2_minus := n_X_μ2_minus par meas
  let n_X_μ1_plus := n_X_μ1_plus par meas
  let s_X0_u := s_X0_u par meas
  M[0, meas.n_X]{
  ((τ1 par) * par.μ1 / (par.μ2 * (par.μ1 - par.μ2)))
    * (n_X_μ2_minus - (par.μ2 ^ 2 / par.μ1 ^ 2)
    * n_X_μ1_plus
    - ((par.μ1 ^ 2 - par.μ2 ^ 2) / (par.μ1 ^ 2) * (s_X0_u / (τ0 par))))
  }

@[approx] lemma mem_approx_s_X1_l : approx (s_X1_l par meas) (Real.s_X1_l par meas) := by
  simp only [Real.s_X1_l, s_X1_l]
  approx

def Phi_Z_u : Interval :=
  let v_X1_u := v_X1_u par meas
  let s_X1_l := s_X1_l par meas
  let s_Z1_l := s_Z1_l par meas
  M[0, 0.5]{
    (v_X1_u / s_X1_l + γ par.ε_sec (v_X1_u / s_X1_l) s_Z1_l s_X1_l)
  }

@[approx] lemma mem_approx_Phi_Z_u : approx (Phi_Z_u par meas) (Real.Phi_Z_u par meas) := by
  simp only [Real.Phi_Z_u, Phi_Z_u]
  approx

def SKL (M_EC : ℕ) : Interval :=
  let s_Z0_l := s_Z0_l par meas
  let Phi_Z_u := Phi_Z_u par meas
  let s_Z1_l := s_Z1_l par meas
  let const_term := - log₂ (2/par.ε_cor) - par.a * log₂ (par.b / par.ε_sec)
  s_Z0_l + s_Z1_l * (1 - binEntropy2 Phi_Z_u) - M_EC + const_term

@[approx] lemma mem_approx_SKL (M_EC : ℕ) :
    approx (SKL par meas M_EC) (Real.SKL par meas M_EC) := by
  simp only [Real.SKL, SKL]
  approx

def secretKeyLength (M_EC : UInt64) : ℕ :=
  let skl : Interval := SKL par meas M_EC.toNat
  skl.natFloor

lemma secretKeyLength_correct (M_EC : UInt64) :
    secretKeyLength par meas M_EC ≤ Real.secretKeyLength par meas M_EC.toNat := by
  simp [secretKeyLength]
  apply natFloor_le
  exact mem_approx_SKL par meas M_EC.toNat

end TakingProtocolParamsAndMeasResult
