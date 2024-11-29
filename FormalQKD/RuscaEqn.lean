/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Basic

/-!
# Secret Key Length Equations

The secret key length is computed from parameters (both freely chosen by the protocol, as well as
properties of the hardware) and measurement results.

This file presents the equation in terms of `Real` numbers
(though inputs and outputs are rational or even natural numbers).
Thus, the equations are useful for studying them and proving theorems about them, e.g. proving how
they realate to the composable security framework of quantum key distribution.

For **computing** a secret key length use `RuscaEqnApprox.lean`!
It approximates these equations using interval arithmetic.

## Tags

QKD, secret, key, length, rate, quantum, key, distribution, post-processing

-/


/-- Clip a value within bounds a and b-/
local notation "M[" a ", " b "]{"c"}" => max a (min b c)

structure MeasResult where
  n_X_μ1 : ℕ
  n_X_μ2 : ℕ
  n_Z_μ1 : ℕ
  n_Z_μ2 : ℕ
  m_X_μ1 : ℕ
  m_X_μ2 : ℕ
  m_Z_μ1 : ℕ
  m_Z_μ2 : ℕ
deriving DecidableEq, Inhabited, Repr

instance isntMeasResultToString : ToString MeasResult where
  toString s := Repr.reprPrec s 1 |> toString

def MeasResult.n_X (r : MeasResult) : ℕ := r.n_X_μ1 + r.n_X_μ2

def MeasResult.m_X (r : MeasResult) : ℕ := r.m_X_μ1 + r.m_X_μ2

def MeasResult.n_Z (r : MeasResult) : ℕ := r.n_Z_μ1 + r.n_Z_μ2

def MeasResult.m_Z (r : MeasResult) : ℕ := r.m_Z_μ1 + r.m_Z_μ2

structure ProtocolParams where
  ε_sec : ℚ := 1e-9
  ε_cor : ℚ := 1e-15
  a     : ℚ := 6
  b     : ℚ := 19
  ε_1   : ℚ := ε_sec / b
  ε_2   : ℚ := ε_sec / b
  P_μ1  : ℚ := 0.7
  μ1    : ℚ := 0.51
  μ2    : ℚ := 0.15

def ProtocolParams.P_μ2 (par : ProtocolParams) : ℚ := 1 - par.P_μ1

noncomputable section

open Real

-- τ(n, μ_1, P_μ1, μ_2, P_μ2) = (
--         (P_μ1 * exp -μ_1) * μ_1 ^ n / factorial(n)) +
--         (P_μ2 * exp -μ_2) * μ_2 ^ n / factorial(n))
--     )

def ProtocolParams.τ0 (par : ProtocolParams) : ℝ :=
  (par.P_μ1 * Real.exp (-par.μ1) ) * 1  + (par.P_μ2 * Real.exp (-par.μ2) ) * 1

def ProtocolParams.τ1 (par : ProtocolParams) : ℝ :=
  (par.P_μ1 * exp (-par.μ1)) * par.μ1 + (par.P_μ2 * exp (-par.μ2)) * par.μ2

namespace Real

/-- Shannon binary entropy function
Mathlib measures Entropy in Nats.
We need entropy measured in bits, hence divide by `log 2`. -/
def binEntropy2 (p : ℝ) : ℝ := Real.binEntropy p / log 2

def γ (a b c d : ℝ) :=
    sqrt ((c + d) * (1 - b) * b / (c * d * log 2.) * log (
           (c + d) * (19 ^ 2) / (c * d * (1 - b) * b * (a * a))
       ) / (log 2.))

def δ (n ϵ : ℝ) := sqrt (n * log (1 / ϵ) / 2)

section TakingProtocolParamsAndMeasResult

variable (par : ProtocolParams)
         (meas : MeasResult)

/-!
### Secret key length equations
-/

def n_Z_μ1_plus : ℝ := exp par.μ1 / par.P_μ1 * (meas.n_Z_μ1 + δ meas.n_Z par.ε_1)
def n_Z_μ1_minus : ℝ := exp par.μ1 / par.P_μ1 * (meas.n_Z_μ1 - δ meas.n_Z par.ε_1)
def n_Z_μ2_plus : ℝ := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 + δ meas.n_Z par.ε_1)
def n_Z_μ2_minus : ℝ := exp par.μ2 / par.P_μ2 * (meas.n_Z_μ2 - δ meas.n_Z par.ε_1)
def n_X_μ1_plus : ℝ := exp par.μ1 / par.P_μ1 * (meas.n_X_μ1 + δ meas.n_X par.ε_1)
def n_X_μ2_minus : ℝ := exp par.μ2 / par.P_μ2 * (meas.n_X_μ2 - δ meas.n_X par.ε_1)
def m_X_μ1_plus : ℝ := exp par.μ1 / par.P_μ1 * (meas.m_X_μ1 + δ meas.m_X par.ε_1)
def m_X_μ2_minus : ℝ := exp par.μ2 / par.P_μ2 * (meas.m_X_μ2 - δ meas.m_X par.ε_1)

def s_Z0_u : ℝ := 2 *
  (((par.τ0 * exp par.μ2) / par.P_μ2 * (meas.m_Z_μ2 + δ meas.m_Z par.ε_2)) + δ meas.n_Z par.ε_1)

def s_X0_u : ℝ :=   M[0, meas.n_X]{
    2 * (((par.τ0 * exp par.μ2) / par.P_μ2 * (meas.m_X_μ2 + δ meas.m_X par.ε_2)) + δ meas.n_X par.ε_1)
  }

def v_X1_u : ℝ :=
  let m_X_μ1_plus := m_X_μ1_plus par meas
  let m_X_μ2_minus := m_X_μ2_minus par meas
  M[0, meas.n_X]{
    (par.τ1 * (m_X_μ1_plus - m_X_μ2_minus) / (par.μ1 - par.μ2))
  }

def s_Z0_l : ℝ :=
  let n_Z_μ2_minus := n_Z_μ2_minus par meas
  let n_Z_μ1_plus := n_Z_μ1_plus par meas
  M[0, meas.n_Z]{
    par.τ0 / (par.μ1 - par.μ2) * (par.μ1 * n_Z_μ2_minus - par.μ2 * n_Z_μ1_plus)
  }

def s_Z1_l : ℝ :=
  let s_Z0_u := s_Z0_u par meas
  let n_Z_μ2_minus := n_Z_μ2_minus par meas
  let n_Z_μ1_plus := n_Z_μ1_plus par meas
  let μ1 := par.μ1
  let μ2 := par.μ2
  M[0, meas.n_Z]{
    (par.τ1 * μ1 / (μ2 * (μ1 - μ2)))
      * (n_Z_μ2_minus - (μ2 ^ 2 / μ1 ^ 2)
      * n_Z_μ1_plus
      - ((μ1 ^ 2 - μ2 ^ 2) / (μ1 ^ 2) * (s_Z0_u / par.τ0)))
  }

def s_X1_l : ℝ :=
  let n_X_μ2_minus := n_X_μ2_minus par meas
  let n_X_μ1_plus := n_X_μ1_plus par meas
  let s_X0_u := s_X0_u par meas
  M[0, meas.n_X]{
    (par.τ1 * par.μ1 / (par.μ2 * (par.μ1 - par.μ2)))
              * (n_X_μ2_minus - (par.μ2 ^ 2 / par.μ1 ^ 2)
      * n_X_μ1_plus
      - ((par.μ1 ^ 2 - par.μ2 ^ 2) / (par.μ1 ^ 2) * (s_X0_u / par.τ0)))
  }

def Phi_Z_u : ℝ :=
  let v_X1_u := v_X1_u par meas
  let s_X1_l := s_X1_l par meas
  let s_Z1_l := s_Z1_l par meas
  M[0, 0.5]{
    (v_X1_u / s_X1_l + γ par.ε_sec (v_X1_u / s_X1_l) s_Z1_l s_X1_l)
  }

abbrev log₂ (x : ℝ) : ℝ := Real.logb 2 x

def SKL (M_EC : ℕ) : ℝ :=
  let s_Z0_l := s_Z0_l par meas
  let Phi_Z_u := Phi_Z_u par meas
  let s_Z1_l := s_Z1_l par meas
  let const_term := - log₂ (2 / par.ε_cor) - par.a * log₂ (par.b / par.ε_sec)
  s_Z0_l + s_Z1_l * (1 - binEntropy2 Phi_Z_u) - M_EC + const_term

def secretKeyLength (M_EC : ℕ) : ℕ :=
  let skl := SKL par meas M_EC
  Nat.floor skl  -- greatest natural that is less or equal than skl

end TakingProtocolParamsAndMeasResult

end Real
