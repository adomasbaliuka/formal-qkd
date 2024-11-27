/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import FormalQKD

namespace TEST  --------------------------------------------------------------------- TEST

open Sifting
open State

def a1 := #[H, M, M, H, V]
def a2 := #[H, V, V, H, H]


#eval siftBasis a1 a2 (by rfl)

lemma samesize : a1.size = a2.size := by rfl

#eval countErrors a1 a2 samesize
#eval countBasisMatches a1 a2 samesize
#eval QBER a1 a2 samesize


end TEST
