import Init.Data.Nat.Div
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas

import Time.Data.Nat.Lemmas

/-!
# Additional integer lemmas.
-/

namespace Int

open Int

protected theorem of_nat_sub_add_eq {a b c : Nat} (h :  b ≤ a)
    : ofNat a - ofNat b + ofNat c = ofNat (a - b + c) := by
  have : ofNat (a - b) = ofNat a - ofNat b := Int.ofNat_sub h
  rw [← this]
  rfl

protected theorem of_nat_add_sub_eq {a b c : Nat} (h :  c ≤ a + b)
    : ofNat a + ofNat b - ofNat c = ofNat (a + b - c) := by
  have : ofNat a + ofNat b = ofNat (a + b) := Int.ofNat_add a b
  rw [this]
  have :  ofNat (a + b - c) = ofNat (a + b) - ofNat c := @Int.ofNat_sub c (a + b) h
  exact id (Eq.symm this)

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
      rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe] at heq
      have : ofNat b - ofNat b / ofNat c + ofNat b / ofNat d = ofNat (b - b / c + b / d) := by
        have : ofNat b / ofNat c = ofNat (b / c) := rfl
        rw [this]
        have := @Int.ofNat_sub (b / c) b (by exact Nat.div_le_self b c)
        simp_all
      rw [this] at heq
      exact Int.ofNat_inj.mp heq
    simp_all
  · contradiction
  · omega
  · contradiction

protected theorem tdiv_sub_eq_div_sub {a b c d : Nat}
  (h : a = ((b:Int) - (b:Int).tdiv c).tdiv d) (hle : 0 ≤ (b:Int) - (b:Int).tdiv c)
    : a = (b - b / c) / d := by
  simp [@Int.tdiv_sub_add_eq_div_sub_add a b c 0 d (by simp [h]) (by simp [hle])]

protected theorem tdiv_of_nat_le {a b : Nat} : 0 ≤ Int.tdiv (ofNat a) (ofNat b) := by
  exact le.intro_sub (a / b + 0) rfl

protected theorem tdiv_of_nat_le_div {a b c : Nat} (h : Int.tdiv (ofNat a) (ofNat b) ≤ ofNat c)
    : a / b ≤ c := by
  exact ofNat_le.mp h

protected theorem div_le_tdiv_of_nat {a b c : Nat} (h : a / b ≤ c)
    : Int.tdiv (ofNat a) (ofNat b) ≤ ofNat c := by
  simp [Int.tdiv]
  omega

protected theorem le_div_tdiv_of_nat {a b c : Nat} (h : a ≤ b / c)
    : ofNat a ≤ Int.tdiv (ofNat b) (ofNat c) := by
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
      have : Int.neg (Int.negSucc n) ≤ (↑((m' + 1).div n') * (↑w + 1)) := by
        have : Int.neg (Int.negSucc n) = Nat.succ n := rfl
        rw [this, ← h]
        have h1 : n + w = m' := Int.sub_eq_add_of_int n w m' heq'
        have h2 : n' = w + 1 := by omega
        rw [← h1, h2]
        have := Nat.succ_le_div_mul n w
        omega
      exact Int.neg_le_neg this
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
      have : ↑((m' + 1).div n') * (↑w + 1) ≤ Int.neg (Int.negSucc m') := by
        have : Int.neg (Int.negSucc m') = Nat.succ m' := rfl
        rw [this, ← h]
        have : (m' + 1).div n' * n' ≤ m'.succ := by
          rw [Nat.div_mul_eq_sub_mod (m' + 1) n']
          omega
        omega
      exact Int.neg_le_neg this
    · contradiction

protected theorem add_mul_tmod_self {a b c : Int} (ha : 0 ≤ a) (habc : 0 ≤ a + b * c)
    : (a + b * c).tmod c = a.tmod c := by
  rw [@Int.tmod_eq_emod (a + b * c) c, @Int.tmod_eq_emod a c]
  simp_all [Int.add_mul_emod_self]

protected theorem ofNat_eq_natCast (n : Nat) : Int.ofNat n = (n:Int) := rfl

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
