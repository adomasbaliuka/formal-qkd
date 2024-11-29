/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import FormalQKD.RuscaEqn
import Interval
import Interval.NatFloor
import Mathlib.Tactic.Basic

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

/-!
### Definitions of minimum and maximum using interval arithmetic
-/

section MinMaxAbs

variable (α : Type) [LinearOrderedField α]
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

section NaturalPowers

/-- Natural powers
* allows negative inputs
* more precise for small powers
-/
def Interval.pown (x : Interval) (n : ℕ) : Interval := match n with
  | 0 => 1
  | n + 1 => x * x.pown n

/-- Enable `_ ^ _` notation.
-- Nevertheless, use the "normal" `pow` that takes `Interval` exponenets -/
instance istHPowIntervalNat : HPow Interval ℕ Interval where
  hPow x n := x.pow (.ofNat n)

/-- `Interval.pow` is conservative for `ℕ` powers -/
@[approx] lemma Interval.mem_approx_pow_nat' {x : Interval} {n : ℕ} {x' : ℝ}
    (xm : x' ∈ approx x) : x' ^ n ∈ approx (x ^ n) := by
  simp only [← Real.rpow_natCast]
  have : x ^ n = x.pow (.ofNat n) := by unfold HPow.hPow; rfl
  rw [this]
  apply Interval.mem_approx_pow xm
  exact approx_ofNat n

end NaturalPowers
namespace MyComputable

open Interval

/-- Clip a value within bounds a and b-/
local notation "M[" a ", " b "]{"c"}" => max a (min b c)

@[approx] lemma mem_approx_natCast (n : ℕ) : (n : ℝ) ∈ approx (n : Interval) := by
  have : approx (n : Interval) = approx (Interval.ofNat n) := by simp [Nat.cast, NatCast.natCast]
  rw [this]
  approx

def Interval.max (a b : Interval) := 1/2 * (a + b) + 1/2 * abs (a - b)

instance instMaxInterval : Max Interval where
  max := Interval.max

def Interval.min (a b : Interval) := 1/2 * (a + b) - 1/2 * abs (a - b)

instance instMinInterval : Min Interval where
  min := Interval.min

-- TODO might be actually equal to the min above!
-- def betterMin (a b : Interval) : Interval :=
--   {
--     lo := min a.lo b.lo
--     hi := min a.hi b.hi
--     norm := by simp_all only [Floating.min_eq_nan, lo_eq_nan, hi_eq_nan]
--     le' := by
--       intros
--       simp_all only [ne_eq, Floating.min_eq_nan, lo_eq_nan, not_or, hi_eq_nan,
--         not_false_eq_true, Floating.val_min, le_min_iff, min_le_iff, le, true_or, or_true, and_self]
--   }

@[approx] lemma mem_approx_min {a b : ℝ} {a' b' : Interval}
    (ha : a ∈ approx a') (hb : b ∈ approx b') :
    min a b ∈ approx (Interval.min a' b') := by
  rw [min_eq_sum_sub_abs, Interval.min]
  approx

@[approx] lemma mem_approx_max {a b : ℝ} {a' b' : Interval}
    (ha : a ∈ approx a') (hb : b ∈ approx b') :
    max a b ∈ approx (Interval.max a' b') := by
  rw [max_eq_sum_add_abs, Interval.max]
  approx

@[approx] lemma mem_approx_maxmin {n : ℕ} {a : ℝ} (a' : Interval) (ha : a ∈ approx a') :
    M[0, (n : ℝ)]{a} ∈ approx (M[0, (n : Interval)]{a'}) := by
  apply mem_approx_max
  · exact mem_approx_zero
  · apply mem_approx_min
    · apply approx_ofNat
    · assumption

@[approx] lemma mem_approx_maxmin' {n a : ℝ} {a' n' : Interval}
    (ha : a ∈ approx a') (hn : n ∈ approx n'):
    M[0, (n : ℝ)]{a} ∈ approx (M[0, n']{a'}) := by
  apply mem_approx_max
  · exact mem_approx_zero
  · apply mem_approx_min <;> assumption

instance : ToString Floating where
  toString f := f.toFloat.toString

instance instToStringInterval : ToString Interval where
  toString x := bif x = nan then "nan" else "[" ++ (toString x.lo) ++ "," ++ (toString  x.hi) ++ "]"

abbrev logb (b x : Interval) : Interval := log x / log b
abbrev log₂ (x : Interval) : Interval := logb 2 x

@[approx] lemma mem_approx_log₂ {x : Interval} {a : ℝ}
    (ax : a ∈ approx x) : Real.log₂ a ∈ approx (log₂ x) := by
  rw [log₂, Real.log₂, Real.logb, logb]
  approx

/-!
### Auxilliary definitions (in terms of `Interval`)
-/

def binEntropy2 (p : Interval) := (-p * log p - (1 - p) * log (1 - p)) / log 2

/-- `binEntropy` is conservative -/
@[approx] lemma mem_approx_binEntropy {x : Interval} {a : ℝ}
    (ax : a ∈ approx x) : Real.binEntropy2 a ∈ approx (binEntropy2 x) := by
  simp only [binEntropy2, Real.binEntropy2, Real.binEntropy, Real.log_inv, mul_neg]
  have : (-(a * Real.log a) + -((1 - a) * Real.log (1 - a))) =
    (-a * a.log - (1 - a) * (1 - a).log) := by ring
  rw [this]
  approx

def γ (a b c d : Interval) :=
    sqrt ((c + d) * (1 - b) * b / (c * d * log 2.) * log (
           (c + d) * (19 ^ 2) / (c * d * (1 - b) * b * (a * a))
       ) / (log 2.))

/-- `binEntropy` is conservative -/
@[approx] lemma mem_approx_γ {ia ib ic id : Interval} {a b c d : ℝ}
    (ia_aprox : a ∈ approx ia)
    (ib_aprox : b ∈ approx ib)
    (ic_aprox : c ∈ approx ic)
    (id_aprox : d ∈ approx id)
    : Real.γ a b c d ∈ approx (γ ia ib ic id) := by
  rw [γ, Real.γ]
  approx

def δ (n ϵ : Interval) := sqrt (n * log (1 / ϵ) / 2)

@[approx] lemma mem_approx_δ {n' ε': Interval} {n ε : ℝ}
    (approxn : n ∈ approx n')
    (approxε : ε ∈ approx ε') :
    Real.δ n ε ∈ approx (δ n' ε') := by
  unfold Real.δ δ
  approx

-- τ(n, μ_1, P_μ1, μ_2, P_μ2) = (
--         (P_μ1 * exp -μ_1) * μ_1 ^ n / factorial(n)) +
--         (P_μ2 * exp -μ_2) * μ_2 ^ n / factorial(n))
--     )

def τ0 (par : ProtocolParams) : Interval :=
  ((par.P_μ1) * exp (- par.μ1) ) * 1  + (par.P_μ2 * exp (- par.μ2) ) * 1

@[approx] lemma mem_approx_τ0 (par : ProtocolParams) :
    ProtocolParams.τ0 par ∈ approx (MyComputable.τ0 par ) := by
  simp only [ProtocolParams.τ0, MyComputable.τ0]
  approx

def τ1 (par : ProtocolParams) : Interval :=
  ((par.P_μ1) * exp (-par.μ1)) * (par.μ1) + (par.P_μ2 * exp (- par.μ2)) * par.μ2

@[approx] lemma mem_approx_τ1 (par : ProtocolParams) :
    ProtocolParams.τ1 par ∈ approx (MyComputable.τ1 par ) := by
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
    Real.n_Z_μ1_plus par meas ∈ approx (n_Z_μ1_plus par meas) := by
  simp only [Real.n_Z_μ1_plus, n_Z_μ1_plus]
  approx

def n_Z_μ1_minus : Interval := exp par.μ1 / par.P_μ1 * (meas.n_Z_μ1 - δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ1_minus :
    Real.n_Z_μ1_minus par meas ∈ approx (n_Z_μ1_minus par meas) := by
  simp only [Real.n_Z_μ1_minus, n_Z_μ1_minus]
  approx

def n_Z_μ2_plus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 + δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ2_plus :
    Real.n_Z_μ2_plus par meas ∈ approx (n_Z_μ2_plus par meas) := by
  simp only [Real.n_Z_μ2_plus, n_Z_μ2_plus]
  approx

def n_Z_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 - δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_n_Z_μ2_minus :
    Real.n_Z_μ2_minus par meas ∈ approx (n_Z_μ2_minus par meas) := by
  simp only [Real.n_Z_μ2_minus, n_Z_μ2_minus]
  approx

def n_X_μ1_plus : Interval := exp par.μ1 / par.P_μ1 * (meas.n_X_μ1 + δ meas.n_X par.ε_1)

@[approx] lemma mem_approx_n_X_μ1_plus :
    Real.n_X_μ1_plus par meas ∈ approx (n_X_μ1_plus par meas) := by
  simp only [Real.n_X_μ1_plus, n_X_μ1_plus]
  approx

def n_X_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.n_X_μ2 - δ meas.n_X par.ε_1)

@[approx] lemma mem_approx_n_X_μ2_minus :
    Real.n_X_μ2_minus par meas ∈ approx (n_X_μ2_minus par meas) := by
  simp only [Real.n_X_μ2_minus, n_X_μ2_minus]
  approx

def m_X_μ1_plus : Interval := exp par.μ1 / par.P_μ1 * (meas.m_X_μ1 + δ meas.m_X par.ε_1)

@[approx] lemma mem_approx_m_X_μ1_plus :
    Real.m_X_μ1_plus par meas ∈ approx (m_X_μ1_plus par meas) := by
  simp only [Real.m_X_μ1_plus, m_X_μ1_plus]
  approx

def m_X_μ2_minus : Interval := exp par.μ2 / par.P_μ2 * (meas.m_X_μ2 - δ meas.m_X par.ε_1)

@[approx] lemma mem_approx_m_X_μ2_minus :
    Real.m_X_μ2_minus par meas ∈ approx (m_X_μ2_minus par meas) := by
  simp only [Real.m_X_μ2_minus, m_X_μ2_minus]
  approx

def s_Z0_u : Interval := 2 *
  ((((τ0 par) * exp par.μ2) / par.P_μ2 * (meas.m_Z_μ2 + δ meas.m_Z par.ε_2)) + δ meas.n_Z par.ε_1)

@[approx] lemma mem_approx_s_Z0_u :
    Real.s_Z0_u par meas ∈ approx (s_Z0_u par meas) := by
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
    Real.s_X0_u par meas ∈ approx (s_X0_u par meas) := by
  simp only [Real.s_X0_u, s_X0_u]
  approx

def v_X1_u : Interval :=
  let m_X_μ1_plus := m_X_μ1_plus par meas
  let m_X_μ2_minus := m_X_μ2_minus par meas
  M[0, meas.n_X]{
    ((τ1 par) * (m_X_μ1_plus - m_X_μ2_minus) / (par.μ1 - par.μ2))
  }

@[approx] lemma mem_approx_v_X1_u : Real.v_X1_u par meas ∈ approx (v_X1_u par meas) := by
  simp only [Real.v_X1_u, v_X1_u]
  approx

def s_Z0_l : Interval :=
  let n_Z_μ2_minus := n_Z_μ2_minus par meas
  let n_Z_μ1_plus := n_Z_μ1_plus par meas
  M[0, meas.n_Z]{
    (τ0 par) / (par.μ1 - par.μ2) * (par.μ1 * n_Z_μ2_minus - par.μ2 * n_Z_μ1_plus)
  }

@[approx] lemma mem_approx_s_Z0_l : Real.s_Z0_l par meas ∈ approx (s_Z0_l par meas) := by
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

@[approx] lemma mem_approx_s_Z1_l : Real.s_Z1_l par meas ∈ approx (s_Z1_l par meas) := by
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

@[approx] lemma mem_approx_s_X1_l : Real.s_X1_l par meas ∈ approx (s_X1_l par meas) := by
  simp only [Real.s_X1_l, s_X1_l]
  approx

def Phi_Z_u : Interval :=
  let v_X1_u := v_X1_u par meas
  let s_X1_l := s_X1_l par meas
  let s_Z1_l := s_Z1_l par meas
  M[0, 0.5]{
    (v_X1_u / s_X1_l + γ par.ε_sec (v_X1_u / s_X1_l) s_Z1_l s_X1_l)
  }

@[approx] lemma mem_approx_Phi_Z_u : Real.Phi_Z_u par meas ∈ approx (Phi_Z_u par meas) := by
  simp only [Real.Phi_Z_u, Phi_Z_u]
  approx

def SKL (M_EC : ℕ) : Interval := -- TODO make Nat
  let s_Z0_l := s_Z0_l par meas
  let Phi_Z_u := Phi_Z_u par meas
  let s_Z1_l := s_Z1_l par meas
  let const_term := - log₂ (2/par.ε_cor) - par.a * log₂ (par.b / par.ε_sec)
  s_Z0_l + s_Z1_l * (1 - binEntropy2 Phi_Z_u) - M_EC + const_term

@[approx] lemma mem_approx_SKL (M_EC : ℕ) :
    (Real.SKL par meas M_EC) ∈ approx (SKL par meas M_EC) := by
  simp only [Real.SKL, SKL]
  approx

def secretKeyLength (M_EC : UInt64) : ℕ :=
  let skl : Interval := SKL par meas M_EC.toNat
  skl.natFloor

lemma secretKeyLength_correct (M_EC : UInt64) :
    secretKeyLength par meas M_EC ≤ Real.secretKeyLength par meas M_EC.toNat := by
  simp [secretKeyLength]
  apply Interval.le_natFloor
  exact mem_approx_SKL par meas M_EC.toNat

end TakingProtocolParamsAndMeasResult
