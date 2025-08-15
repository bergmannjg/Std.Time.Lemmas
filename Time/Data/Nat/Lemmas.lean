
/-!
# Additional natural number lemmas.
-/

namespace Nat

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
    grind
  rw [← this]
  rw [Nat.div_mul_eq_sub_mod n (w + 1)]
  have : n % (w + 1) ≤ w := by
    have : n % (w + 1) < w + 1 := Nat.mod_lt n (zero_lt_succ w)
    exact le_of_lt_succ this
  omega
