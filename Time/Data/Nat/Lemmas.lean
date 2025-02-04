
/-!
# Additional natural number lemmas.
-/

namespace Nat

protected theorem div_one_le (a b : Nat) (hle : a ≤ b) (hlt : 0 < a) : 1 ≤ b.div a := by
  have ⟨k, h⟩  := @Nat.le.dest a b hle
  rw [← h]
  have := @Nat.add_div_left k a hlt
  simp [instHDiv, Nat.instDiv] at this
  rw [this]
  exact le_add_left 1 (k.div a)

protected theorem div_mul_eq_sub_mod (n w : Nat) : n.div w * w = n - n % w := by
  have : n.div w * w + n % w = n := by
    have := Nat.div_add_mod n w
    rw [Nat.mul_comm] at this
    exact this
  exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm this)))

protected theorem succ_le_div_mul (n w : Nat)
    : n.succ ≤ ((n + w + 1).div (w + 1)) * (w + 1) := by
  have : (n + w + 1).div (w + 1) = n.div (w + 1) + 1 := by
    have : (n + w + 1).div (w + 1) = (n + w + 1 - (w + 1)).div (w + 1) + 1 :=
      @Nat.div_eq_sub_div (w+1) (n + w + 1) (zero_lt_succ w) (le_add_left (w + 1) n)
    simp [] at this
    exact this
  rw [this]

  have : n.div (w + 1) * (w + 1) + w + 1 = (n.div (w + 1) + 1) * (w + 1) := by
    exact Eq.symm (succ_mul_succ (n.div (w + 1)) w)
  rw [← this]

  rw [Nat.div_mul_eq_sub_mod n (w + 1)]
  have : n % (w + 1) ≤ w := by
    have : n % (w + 1) < w + 1 := Nat.mod_lt n (zero_lt_succ w)
    exact le_of_lt_succ this
  omega

protected theorem div_mul_lt {a b n : Nat} (hlt : 0 < b) (h : a / b = n)
    : n * b ≤ a ∧ a < (n + 1) * b := by
  simp [(@Nat.le_div_iff_mul_le b n a hlt).mp (Nat.le_of_eq (id (Eq.symm h)))]
  simp [(@Nat.div_lt_iff_lt_mul b a (n+1) hlt).mp (by omega)]

protected theorem div_eq_zero_lt {a b : Nat} (hlt : 0 < b) (hzero : a / b = 0) : a < b :=
  lt_of_div_eq_zero hlt hzero
