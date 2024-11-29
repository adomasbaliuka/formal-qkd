/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import FormalQKD.RuscaEqnApprox

/- Example values for testing -/
def myPar : ProtocolParams where
  -- just default values!

/- Example values for testing -/
def myMeas : MeasResult where
  n_Z_μ1 := 8875913
  n_Z_μ2 := 1124087
  n_X_μ1 := 165048
  n_X_μ2 := 20902
  m_Z_μ1 := 185856
  m_Z_μ2 := 26055
  m_X_μ1 := 3456
  m_X_μ2 := 484

def isSmall (x : Interval) (ε : Float := 1e-8) : Bool :=
  x.abs.hi.toFloat < ε

section TestNumericSKL

open MyComputable

#print "Checking example values."

#guard isSmall (0.499915958 - binEntropy2 0.11)
#guard isSmall (7.717529454187349 - γ 0.1 0.1 0.1 0.1)
#guard isSmall (83.11290681 - δ 1000 1e-6)
#guard isSmall (2.1141564840596016e7 - n_Z_μ1_plus myPar myMeas)
#guard isSmall (2.1089805919420347e7 - n_Z_μ1_minus myPar myMeas)
#guard isSmall (4.395472030980807e6 - n_Z_μ2_plus myPar myMeas)
#guard isSmall (4.31121309172391e6 - n_Z_μ2_minus myPar myMeas)
#guard isSmall (396176.12935093784 - n_X_μ1_plus myPar myMeas)
#guard isSmall (75203.94317833845 - n_X_μ2_minus myPar myMeas)
#guard isSmall (8735.473153448527 - m_X_μ1_plus myPar myMeas)
#guard isSmall (1038.1798167212369 - m_X_μ2_minus myPar myMeas)
#guard isSmall (167020.1792587285 - s_Z0_u myPar myMeas)
#guard isSmall (6645.523136846764 - s_X0_u myPar myMeas)
#guard isSmall (5411.812583855381 - v_X1_u myPar myMeas)
#guard isSmall (0.0 - s_Z0_l myPar myMeas)
#guard isSmall (5.396516268816283e6 - s_Z1_l myPar myMeas)
#guard isSmall (76462.2755485758 - s_X1_l myPar myMeas)
#guard isSmall (0.07917365937798954 - Phi_Z_u myPar myMeas)
#guard isSmall (1.4647190887320058e6 - SKL myPar myMeas 1776924)

end TestNumericSKL
