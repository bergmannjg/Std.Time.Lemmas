import Init.Data.Nat.Div
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas

import Time.Data.Nat.Lemmas

/-!
# Additional integer lemmas.
-/

namespace Int

open Int

protected theorem sub_tdiv_eq_tmod (a b : Int) : a - (a.tdiv b) * b = tmod a b := by
  rw [Int.mul_comm]
  exact Eq.symm (tmod_def a b)

protected theorem tdiv_sub_add_eq_div_sub_add {a b c d e : Nat}
  (h : a = ((b:Int) - (b:Int).tdiv c + (b:Int).tdiv d).tdiv e)
  (hle : 0 ≤ (b:Int) - (b:Int).tdiv c + (b:Int).tdiv d)
    : a = (b - b / c + b / d) / e := by
  have hle : 0 ≤ (b:Int) - b / c + b /d := hle
  simp [Int.tdiv] at h
  split at h
  · rename_i m n heq hn
    have : a = m / e := by
      rw [← Int.ofNat_inj.mp hn] at h
      exact ofNat_inj.mp h
    have : b - b / c + b / d = m := by
      rw [← Int.ofNat_eq_natCast, ← Int.ofNat_eq_natCast, ← Int.ofNat_eq_natCast] at heq
      have : ofNat b - ofNat b / ofNat c + ofNat b / ofNat d = ofNat (b - b / c + b / d) := by
        have : ofNat b / ofNat c = ofNat (b / c) := rfl
        rw [this]
        have := @Int.ofNat_sub (b / c) b (by exact Nat.div_le_self b c)
        simp_all
      simp_all
      exact Int.ofNat_inj.mp (by omega)
    simp_all
  · contradiction
  · omega
  · contradiction

protected theorem tdiv_sub_eq_div_sub {a b c d : Nat}
  (h : a = ((b:Int) - (b:Int).tdiv c).tdiv d) (hle : 0 ≤ (b:Int) - (b:Int).tdiv c)
    : a = (b - b / c) / d := by
  simp [@Int.tdiv_sub_add_eq_div_sub_add a b c 0 d (by simp [h]) (by simp_all)]

protected theorem tdiv_of_nat_le {a b : Nat} : 0 ≤ Int.tdiv (ofNat a) (ofNat b) := by
  exact le.intro_sub (a / b + 0) rfl

protected theorem tdiv_of_nat_le_div {a b c : Nat} (h : Int.tdiv (ofNat a) (ofNat b) ≤ ofNat c)
    : a / b ≤ c := by
  exact ofNat_le.mp h

protected theorem div_le_tdiv_of_nat {a b c : Nat} (h : a / b ≤ c)
    : Int.tdiv (ofNat a) (ofNat b) ≤ ofNat c := by
  simp [Int.tdiv]
  omega

protected theorem neg_ofNat_eq_negSucc {n : Nat} (hlt : 0 < n) : -(n : Int) = -[n - 1+1] := by
  omega

protected theorem sub_eq_add_of_int (n w m' : Nat) (heq : -[n +1]  - ↑w = -[m' +1])
    : n + w = m' := by
  omega

protected theorem sub_tdiv_mul_le (a b : Int) (ha : a < 0) (hb : 1 < b)
    : ((a - (b - 1)).tdiv b) * b ≤ a := by
  match a, b, @eq_succ_of_zero_lt b (by omega) with
  | Int.negSucc n, (m : Nat), ⟨_, _⟩ =>
    rename_i w h
    simp [tdiv, instHDiv, Nat.instDiv]
    split <;> simp_all
    · omega
    · contradiction
    · rename_i m' n' heq' heq
      norm_cast
      norm_cast at h
      have hle : Int.neg (Int.negSucc n) ≤ (↑((m' + 1).div n') * ↑(w + 1)) := by
        have : Int.neg (Int.negSucc n) = Nat.succ n := rfl
        rw [this, ← h]
        have h1 : n + w = m' := Int.sub_eq_add_of_int n w m' heq'
        have h2 : n' = w + 1 := by norm_cast at h
        rw [← h1, h2]
        have := Nat.succ_le_div_mul n w
        omega

      generalize ((m' + 1).div n' : Int) = x at hle
      generalize (↑(w + 1) : Int) = y at hle

      have : -(x * y) = -x * y := Int.neg_mul_eq_neg_mul x y
      rw [← this]

      have hn := Int.neg_le_neg hle
      have : -[n+1] = - (-[n+1].neg) := rfl
      rw [← this] at hn
      exact hn
    · contradiction

protected theorem le_sub_tdiv_mul (a b : Int) (ha : a < 0) (hb : 1 < b)
    : a - (b - 1) ≤ ((a - (b - 1)).tdiv b) * b := by
  match a, b, @eq_succ_of_zero_lt b (by omega) with
  | Int.negSucc n, (m : Nat), ⟨_, _⟩ =>
    rename_i w h
    simp [tdiv, instHDiv, Nat.instDiv]
    split <;> simp_all
    · omega
    · contradiction
    · rename_i m' n' heq' heq
      have hle : ↑((m' + 1).div n') * (↑w + 1) ≤ Int.neg (Int.negSucc m') := by
        have : Int.neg (Int.negSucc m') = Nat.succ m' := rfl
        rw [this, ← h]
        have : (m' + 1).div n' * n' ≤ m'.succ := by
          rw [Nat.div_mul_eq_sub_mod (m' + 1) n']
          omega
        omega

      generalize ((m' + 1).div n' : Int) = x at hle
      generalize ((w:Int) + 1) = y at hle

      have hn := Int.neg_le_neg hle
      have : -[m'+1] = - (-[m'+1].neg) := rfl
      rw [← this] at hn

      have : -(x * y) = -x * y := by exact Int.neg_mul_eq_neg_mul x y
      rw [this] at hn
      exact hn
    · contradiction

protected theorem mod_zero_of_add_mul_eq_iff (a b c : Int)
    : a.tmod c = 0 ↔ (a + c * b).tmod c = 0  :=
  Iff.intro
  (fun h => by
    have h1 := Int.dvd_iff_tmod_eq_zero.mpr h
    have h2 := Int.dvd_mul_right c b
    have h3 := Int.dvd_add h1 h2
    exact Int.dvd_iff_tmod_eq_zero.mp h3)
  (fun h => by
    have h1 := Int.dvd_iff_tmod_eq_zero.mpr h
    have h2 := Int.dvd_mul_right c b
    have h3 := (@Int.dvd_add_left c a (c * b) h2).mp h1
    exact (@Int.dvd_iff_tmod_eq_zero c a).mp h3)

protected theorem sub_tdiv_mul_le_pred {a : Int} {n : Nat}
    : a - a.tdiv (n + 1) * (n + 1) ≤ n := by
  rw [Int.sub_tdiv_eq_tmod a (n + 1)]
  exact Int.lt_add_one_iff.mp (@Int.tmod_lt_of_pos a (n + 1) (succ_ofNat_pos n))

protected theorem tdiv_of_sub_tdiv_eq_ofNat {a : Int} {k l: Nat} (ha : 0 ≤ a)
    : (a - a.tdiv l).tdiv k = Int.ofNat ((a.toNat - a.toNat / l) / k) := by
  generalize h : a.toNat = n
  unfold Int.tdiv
  split <;> simp_all
  rename_i heq' heq
  split at heq' <;> simp_all
  · expose_names
    rw [← heq', @Int.natCast_sub (n / l) n (Nat.div_le_self n l), ← heq_1]
    simp
  · expose_names
    split at heq <;> try simp_all <;> try omega
    expose_names
    have hle : 0 ≤ n - (n / n_2 : Int) := by
      norm_cast
      have := Nat.div_le_self n n_2
      omega
    rw [heq] at hle
    contradiction

protected theorem tdiv_of_sub_tdiv_add_tdiv_eq_ofNat {k l m : Nat} {a : Int} (h : l ≤ a)
    : (a - a.tdiv k + a.tdiv l).tdiv m = Int.ofNat (a.toNat - a.toNat / k + a.toNat / l) / m := by
  generalize h : a.toNat = n
  unfold Int.tdiv
  split <;> simp_all
  · expose_names
    split at heq <;> simp_all
    · expose_names
      rw [← heq_2] at heq
      have := @Int.natCast_sub (n / k) n (Nat.div_le_self n k)
      rw [this]
      rw [← heq]
      simp
    · omega
  · expose_names
    split at heq <;> simp_all
    · expose_names
      have hle : 0 ≤ (n : Int) - n / n_2 + n / l := by
        have : 0 ≤ (n : Int) / l := by
          norm_cast
          exact Nat.zero_le (n / l)
        have := Nat.div_le_self n n_2
        omega
      rw [heq] at hle
      contradiction
    · omega
