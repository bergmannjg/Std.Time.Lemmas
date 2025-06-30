
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

-- see Std.Time.Verification.tdiv_of_sub_tdiv_le
example {n : Nat} (h1 : 1460 ≤ n) (h2: n ≤ 36523) : (n - n / 1460) / 365 < 100 := by
  exact @Nat.div_of_sub_div_lt n 365 4 100 (by omega) (by omega) ⟨25, by omega⟩ (by omega)

theorem sub_succ_add {n k : Nat} (h : k < n) : n - k.succ + k = n - 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Nat.add_comm k 1, ← Nat.add_succ 1 k]
    rw [← ih (by omega)]
    rw [← @Nat.sub_add_comm n k k.succ (by omega)]
    rw [← @Nat.sub_add_comm n (1 + k) (1 + k.succ) (by omega)]
    rw [Nat.add_comm 1 k, ← Nat.add_assoc]
    omega

theorem add_sub_le_eq (n : Nat) {m k : Nat} (h1 : m < k) (h2 : k < n) : n - k + m = n - (k - m) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hOr :  m < k ∨ m = k := by omega
    cases hOr
    · expose_names
      have := ih h (by omega)
      omega
    · expose_names
      rw [h]
      simp
      rw [← @Nat.succ_eq_add_one k]
      exact sub_succ_add (by omega)

theorem sub_pred {n m : Nat} (h1 : 0 < m) (h2 : m ≤ n): n - pred m = succ (n - m) := by
  unfold Nat.pred
  split
  · contradiction
  · omega

theorem div_of_sub_div_add_div_lt {i j k l m : Nat} (n : Nat)
  (hi : i = j * l + l / k - 1) (hm : m = j * k)
  (h1 : i ≤ n) (h2 : n < j * k * l + l - k) (h3 : k ∣ l)
  (h4 : l - k < j * k) (h5 : k < l) (h6 : l < n) (h7 : m ≤ i)
    : (n - n / m + n / i) / j < k * l := by
  have hjk := zero_lt_of_lt h4
  have hk : 0 < k := Nat.lt_of_mul_lt_mul_left (by simp; exact hjk)
  have hj : 0 < j := Nat.lt_of_mul_lt_mul_left (by simp; rwa [Nat.mul_comm] at hjk)
  have hilt : 0 < i := by rw [hi]; omega
  have : n / i ≤ k - 1 := by
    exact (Nat.div_le_iff_le_mul hilt).mpr (by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left i hk)]
      rw [hi, Nat.mul_sub, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm k j]
      apply Nat.le_of_lt_add_one
      rw [Nat.sub_add_cancel (by omega), Nat.mul_one]
      have : l - k ≤ k * (l / k) - k := by
        rw [Nat.mul_div_cancel' h3]
        exact Nat.le_refl (l - k)
      omega)
  have : k - 1 ≤ j * (k * l) / i := by
    exact (Nat.le_div_iff_mul_le hilt).mpr (by
      rw [Nat.sub_mul, Nat.mul_comm 1 i, Nat.mul_one, hi, Nat.mul_sub, Nat.mul_add]
      rw [← Nat.mul_assoc, Nat.mul_comm k j, Nat.mul_one, Nat.mul_div_cancel' h3]
      rw [← Nat.mul_assoc, Nat.sub_sub]
      simp +arith
      have : 1 ≤ l / k := (Nat.le_div_iff_mul_le hk).mpr (by omega)
      have := Nat.le_mul_of_pos_left l hj
      omega)
  have : n / i ≤ n / m := Nat.div_le_div (Nat.le_refl n) h7 (by omega)
  exact Nat.div_lt_of_lt_mul (by
    have h : n < j * (k * l) ∨ j * (k * l) ≤ n := by omega
    cases h
    · expose_names
      have : n - n / m + n / i ≤ n := by
        have : n / m < l := Nat.div_lt_of_lt_mul (by rw [hm]; rwa [Nat.mul_assoc])
        omega
      exact Nat.lt_of_le_of_lt this h
    · expose_names
      rw [hm]
      have : n / (j * k) = l := by
        have := (@Nat.le_div_iff_mul_le (j * k) l n hjk).mpr
                                    (by rwa [← Nat.mul_assoc, Nat.mul_comm] at h)
        have := (@Nat.div_le_iff_le_mul (j * k) n l hjk).mpr
                                    (by rw [Nat.mul_comm] at h2; omega)
        omega
      rw [this]
      have : n / i = k - 1 := by
        have := @Nat.div_le_div _ _ i i h (by omega) (by exact Nat.ne_zero_of_lt hilt)
        omega
      rw [this, add_sub_le_eq n (by omega) h6]
      have : l - (k - 1) = l - k + 1 := by
        rw [← Nat.pred_eq_sub_one, ← Nat.succ_eq_add_one]
        exact sub_pred (@Nat.lt_of_mul_lt_mul_left j 0 k (by omega)) (le_of_succ_le h5)
      rw [this]
      rw [← Nat.mul_assoc]
      exact (Nat.sub_lt_iff_lt_add (by omega)).mpr (by omega))

-- see Std.Time.Verification.tdiv_of_sub_tdiv_add_tdiv_le
example (n : Nat) (h1 : 36524 ≤ n) (h2 : n < 146096)
    : (n - n / 1460 + n / 36524) / 365 < 400 := by
  exact @Nat.div_of_sub_div_add_div_lt 36524 365 4 100 1460 n (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
