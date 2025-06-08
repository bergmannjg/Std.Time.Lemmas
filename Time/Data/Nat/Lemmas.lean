
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

protected theorem div_lt_of_lt_mul_add {a b c d : Nat} (h1 : d < b) (h2 : a < b * c + d)
    : a / b < c + 1 := by
  have : b * c + d < b * (c + 1) := by
    have : b * (c + 1) = b * c + b := rfl
    omega
  exact Nat.div_lt_of_lt_mul (by omega)

protected theorem div_of_sub_div_lt {n k l j : Nat}
  (hk : 0 < k) (hl : 0 < l) (hm : ∃ m, j = l * m ∧ 0 < m ∧ m < k * l) (h : n < k * j + (j / l))
    : (n - n / (k * l)) / k < j := by
  let ⟨m, ⟨heq, ⟨hlt1, hlt2⟩⟩⟩ := hm
  have hm : j / l = m := by simp_all
  have : n < (k * l) * (j / l) + j / l := by
    rw [hm, Nat.mul_assoc k l m, ← heq]
    simp_all
  have hlt_add : n / (k * l) < (j / l) + 1 := Nat.div_lt_of_lt_mul_add (by omega) (by omega)

  generalize hm' : n / (k * l) = m'

  suffices n - m' < k * j + m' - m' by
    suffices n - n / (k * l) < k * j by
      rw [hm'] at this
      exact Nat.div_lt_of_lt_mul this
    simp at this; rw [hm']; exact this

  exact @Nat.sub_lt_sub_right n (k * j + m') m'
    (by
      expose_names
      have h : n < k * j  ∨ k * j  ≤ n := by omega
      cases h
      · rw [← hm']
        exact Nat.div_le_self n (k * l)
      · have hle : m' * (k * l) ≤ n := by
          suffices n = m' * (k * l) + n % (k * l) by exact (le.intro (Eq.symm this))
          have hmod := @Nat.mod_def n (k * l)
          rw [hm'] at hmod
          have := @Nat.eq_add_of_sub_eq n (k * l * m') (n % (k * l)) (by
            rw [← hm']
            exact Nat.mul_div_le  n (k * l)) (hmod.symm)
          rw [Nat.add_comm, Nat.mul_comm] at this
          exact this

        exact Nat.le_trans (Nat.le_mul_of_pos_right m' (by omega)) hle)
    (by
      expose_names
      have h : n < k * j  ∨ k * j  ≤ n := by omega
      cases h
      · omega
      · rename_i h
        suffices j / l = m' by rwa [← this]
        rw [← hm']
        have h := @Nat.div_le_div_right (k * j) n (k * l) h
        have : k * j / (k * l) = j / l := by
          rw [← Nat.div_div_eq_div_mul (k * j) k l, Nat.mul_div_cancel_left j (by omega)]
        rw [this] at h
        exact (Nat.eq_of_le_of_lt_succ h hlt_add).symm)
