import FormalQKD

set_option autoImplicit false

open Sifting

def parseStates (s : String) : Option (List State) :=
  List.allSome <| (s.stripSuffix "\n").toList.map fun c => State.ofChar c


open State in
def main_count_states : IO Unit := do
  let stdin ← IO.getStdin
  let s <- stdin.getLine
  dbg_trace "{s}"
  let states : Option (List State) := parseStates s
  match states with
  | none => throw (IO.userError "Invalid input!")
  | some _ => pure ()
  let x (s : State) : Option ℕ := do
    countState (←states).toArray s
  let counts := [H,V,P,M,h,v,p,m].map x |> List.allSome
  IO.println s!"Hello! {counts}"

def String.parseMeasResult (s : String) : Option MeasResult := do
  let mys := (String.stripPrefix s "\n").stripSuffix "\n"
  let nums := mys.splitOn
  if nums.length != 8 then failure else
  let num_list? := nums.map String.toNat?
  if let some num_list := num_list?.allSome then
    let meas_result := {
        n_Z_μ1 := ← num_list[0]?
        n_Z_μ2 := ← num_list[1]?
        n_X_μ1 := ← num_list[2]?
        n_X_μ2 := ← num_list[3]?
        m_Z_μ1 := ← num_list[4]?
        m_Z_μ2 := ← num_list[5]?
        m_X_μ1 := ← num_list[6]?
        m_X_μ2 := ← num_list[7]?
          : MeasResult}
    return meas_result
  else
    failure

def NatsecretKeyLength
    (my_parameters : ProtocolParams) (meas_result : MeasResult) (lambda_EC : ℕ) :=
  if lambda_EC > UInt64.max.toNat then
      0
  else
      MyComputable.secretKeyLength my_parameters meas_result (.ofNat lambda_EC)

/-- Proof that the number computed by `NatsecretKeyLength` does not exceed the number
specified in the real-number computation at `Real.secretKeyLength`. -/
lemma NatsecretKeyLength_correct
    (my_parameters : ProtocolParams) (meas_result : MeasResult) (lambda_EC : ℕ) :
    -- this is our prescription how to compute secret key length
    NatsecretKeyLength my_parameters meas_result lambda_EC
      ≤
    -- this is the equations (as "directly" as possible from the paper) in terms of real numbers!
    Real.secretKeyLength my_parameters meas_result lambda_EC := by
  unfold NatsecretKeyLength
  split_ifs
  · exact Nat.zero_le (Real.secretKeyLength my_parameters meas_result lambda_EC)
  · have almost := MyComputable.secretKeyLength_correct my_parameters meas_result (.ofNat lambda_EC)
    have : (UInt64.ofNat lambda_EC).toNat = lambda_EC := by
      have := UInt64.toNat_ofNat lambda_EC
      have : lambda_EC % UInt64.size = lambda_EC := by
        simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, UInt64.toNat_max,
          gt_iff_lt, not_lt, UInt64.toNat_ofNat, Nat.reducePow, Nat.add_one_sub_one]
        linarith
      exact this
    convert almost
    exact this.symm

def computeSKL (lambda_EC_str : String) (meas_detections : String) : IO Unit :=
  if let some lambda_EC := lambda_EC_str.stripSuffix "\n" |> String.toNat? then
    -- we parsed a Nat here, but later we want to use UInt64 inputs.
    if let some meas_result := meas_detections.parseMeasResult then
        let my_parameters : ProtocolParams := {}  -- use default values!
        -- this function accepts (lambda_EC : Nat) and does not exceed the Real-number computation
        -- (see `lemma NatsecretKeyLength_correct`)
        let skl := NatsecretKeyLength my_parameters meas_result lambda_EC
        println! s!"\nComputed: SKL = {skl}"
    else
        throw (IO.userError "Failed to parse 8 numbers!")
  else
    throw (IO.userError "Failed to parse λ_EC!")

-- #eval computeSKL "1776924" "8875913 1124087 165048 20902 185856 26055 3456 484"

def main_SKL : IO Unit := do
  let stdin ← IO.getStdin
  println! "Enter\nn_Z_μ1 n_Z_μ2 n_X_μ1 n_X_μ2 m_Z_μ1 m_Z_μ2 m_X_μ1 m_X_μ2"
  let s ← stdin.getLine
  println! "Enter λ_EC"
  let lambda_EC_str ← stdin.getLine
  computeSKL lambda_EC_str s

/-- MAIN ENTRYPOINT of compiled program! -/
def main := main_SKL
