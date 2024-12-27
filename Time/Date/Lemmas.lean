import Std.Time.Date.PlainDate
import Std.Time.Date.Unit.Year

import Time.Data.Nat.Lemmas
import Time.Data.Int.Lemmas

/-!
# Additional Time lemmas.

main theorem:

* `Std.Time.ofDaysSinceUNIXEpochIsValid`: proof that the date of `Std.Time.ofDaysSinceUNIXEpoch'` is valid.

-/

namespace Std
namespace Time

open Std.Time Int

/-- monthSizes of leap year starting at month 3 -/
def monthSizes (leap : Bool) : { val : Array Nat // val.size = 12 } :=
  ⟨#[31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, if leap then 29 else 28], rfl⟩

/-- day of year of first day of month, starting at month 3 -/
def doy_from_month (mp : Int) : Int := (153 * mp + 2).tdiv  5

/-- month from day of year, starting at month 3 -/
def month_from_doy (doy : Int) : Int :=  (5 * doy + 2).tdiv 153

theorem month_from_doy_of_nat_eq (doy mp : Nat) (heq : month_from_doy (ofNat doy) = ofNat mp)
    : (5 * doy + 2) / 153 = mp := by
  simp [month_from_doy, Int.tdiv] at heq
  split at heq
  · rename_i m' n' heq' hn
    have :  m' / n' = mp := Int.ofNat_inj.mp heq
    rwa [← Int.ofNat_inj.mp hn, ← Int.ofNat_inj.mp heq'] at this
  · contradiction
  · contradiction
  · contradiction

theorem monthSizesLeap_eq_doy_from_month_sub (leap : Bool)
    : ∀ (n : Nat) (h : n ≤ 11), (monthSizes leap).val[n]'(Nat.lt_add_one_of_le h)
                      = if n < 11
                        then doy_from_month (n + 1) - doy_from_month n
                        else (if leap then 366 else 365) - doy_from_month n := by
  cases leap <;> simp_arith [monthSizes, doy_from_month]

theorem monthSizesLeap_le (leap : Bool)
    : ∀ (n : Nat) (h : n ≤ 11),
        28 ≤ (monthSizes leap).val[n]'(by exact Nat.lt_add_one_of_le h)
        ∧ (monthSizes leap).val[n]'(Nat.lt_add_one_of_le h) ≤ 31 := by
  cases leap <;> simp_arith [monthSizes, doy_from_month]

theorem doe_le (z era doe : Int)
  (hera : era = (if z ≥ 0 then z else z - 146096).tdiv 146097) (hdoe : doe = z - era * 146097)
    : 0 ≤ doe ∧ doe ≤ 146096 := by
  simp [hdoe, hera]
  split
  · rename_i h
    rw [Int.sub_tdiv_eq_tmod]
    have := @Int.tmod_lt_of_pos z 146097 (by simp)
    have : z.tmod 146097 ≤ 146096 := lt_add_one_iff.mp this
    simp [this]
    exact tmod_nonneg 146097 h
  · rename_i h
    have : (z - 146096).tdiv 146097 * 146097 ≤ z := Int.sub_tdiv_mul_le z 146097
              (Int.lt_of_not_ge h) (by omega)
    have : z - 146096 ≤ (z - 146096).tdiv 146097 * 146097 := Int.le_sub_tdiv_mul z 146097
              (Int.lt_of_not_ge h) (by omega)
    omega

theorem yoe_le_of_doe_lt_365 {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe < 365)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : 0 = yoe := by
  have : doe.tdiv 365 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 1460 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 36524 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  simp_all

theorem yoe_of_doe_lt_1460 {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 1459)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : yoe = doe.tdiv 365 := by
  have : doe.tdiv 1460 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 36524 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  simp_all

theorem yoe_le_of_doe_lt_1460 {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 1459)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : 0 ≤ yoe ∧ yoe ≤ 3 := by
  have := yoe_of_doe_lt_1460 hdoe hyoe
  have : 0 ≤ doe.tdiv 365 := @Int.tdiv_nonneg doe 365 hdoe.left (le.intro_sub (365 + 0) rfl)
  have : doe.tdiv 365 ≤ 3 := by
    simp [Int.tdiv]
    split <;> simp_all
    rename_i heq _
    rw [← heq]
    omega
  omega

theorem yoe_of_doe_lt_36524  {doe yoe : Int} (hdoe : 1460 ≤ doe ∧ doe ≤ 36523)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : yoe = (doe - doe.tdiv 1460).tdiv 365 ∧  doe.tdiv 1460 ≤ 25 := by
  have hle : 0 ≤ doe := by omega
  have : doe.tdiv 1460 ≤ 25 := by
    unfold Int.tdiv
    split <;> simp_all
    rename_i m n heq
    rw [← heq]
    omega
  have : doe.tdiv 36524 = 0 := Int.tdiv_eq_zero_of_lt hle (by omega)
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt hle (by omega)
  simp_all

theorem yoe_le_of_doe_lt_36524  {doe yoe : Int} (hdoe : 1460 ≤ doe ∧ doe ≤ 36523)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : 0 ≤ yoe ∧ yoe ≤ 99 := by
  have : 0 ≤ doe := by omega
  have := yoe_of_doe_lt_36524 hdoe hyoe
  have : 0 ≤ (doe - doe.tdiv 1460).tdiv 365 :=
    @Int.tdiv_nonneg (doe - doe.tdiv 1460) 365 (by omega) (le.intro_sub (365 + 0) rfl)
  have : (doe - doe.tdiv 1460).tdiv 365 ≤ 99 := by
    unfold Int.tdiv
    split <;> simp_all
    · rename_i heq' heq
      split at heq' <;> simp_all
      rw [← heq]
      rename_i hn' _ _
      rw [← hn'] at heq'
      omega
    · rename_i heq' heq
      rw [← heq]
      omega
  omega

theorem yoe_of_doe_lt_146096 {doe yoe : Int} (hdoe : 36524 ≤ doe ∧ doe ≤ 146095)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524).tdiv 365
      ∧ 25 ≤ doe.tdiv 1460
      ∧ doe.tdiv 1460 ≤ 100
      ∧ doe.tdiv 36524 ≤ 3 := by
  have : 0 ≤ doe := by omega
  have hlt : doe < 146096 := by omega
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt this hlt
  simp_all

  have : 25 ≤ doe.tdiv 1460 := by
    match doe with
    | Int.ofNat _ =>
      rename_i a _
      have h : 36524 ≤ a := Int.ofNat_le.mp hdoe.left
      have : 25  ≤ a / 1460 := by omega
      exact Int.le_div_tdiv_of_nat this

  have : doe.tdiv 1460 ≤ 100 := by
    match doe with
    | Int.ofNat _ =>
      rename_i a _ _
      have h : a < 146096 := Int.ofNat_le.mp hlt
      have : a / 1460 ≤ 100 := by omega
      exact Int.div_le_tdiv_of_nat this

  have : doe.tdiv 36524 ≤ 3 := by
    match doe with
    | Int.ofNat _ =>
      rename_i a _ _ _
      have h : a < 146096 := Int.ofNat_le.mp (by simp; exact hlt)
      have : a / 36524 ≤ 3 := by omega
      exact Int.div_le_tdiv_of_nat this

  simp_all

theorem yoe_le_of_doe_lt_146096 {doe yoe : Int} (hdoe : 36524 ≤ doe ∧ doe ≤ 146095)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : 0 ≤ yoe ∧ yoe ≤ 399 := by
  have : 0 ≤ doe := by omega
  have hlt : doe < 146096 := by omega

  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt this hlt
  have := yoe_of_doe_lt_146096 hdoe hyoe

  have hzero : 0 ≤ doe - doe.tdiv 1460 + doe.tdiv 36524 := by
    have : 0 ≤ doe.tdiv 36524 := by match doe with | Int.ofNat _ => exact Int.tdiv_of_nat_le
    omega
  have : 0 ≤ (doe - doe.tdiv 1460 + doe.tdiv 36524).tdiv 365 :=
      @Int.tdiv_nonneg (doe - doe.tdiv 1460 + doe.tdiv 36524) 365 hzero (le.intro_sub (365 + 0) rfl)
  simp_all

  unfold Int.tdiv
  split
  · rename_i m' n' heq hn
    rw [← Int.ofNat_inj.mp hn]
    split at heq
    · rename_i m'' _ hn'' _ _ hyd
      have : m' / 365 ≤ 399 := by
        rw [← Int.ofNat_inj.mp hn''] at heq
        rw [Int.of_nat_sub_add_eq (Nat.div_le_self m'' 1460)] at heq
        have : m'' - m'' / 1460 + m'' / 36524 =  m' := Int.ofNat_inj.mp heq
        have : m' < 146000 := by
          rw [← this]
          have : m'' / 36524 ≤ 3 := Int.tdiv_of_nat_le_div hyd.right.right.right
          omega
        omega
      exact Int.ofNat_le.mpr this
    · contradiction
    · contradiction
    · contradiction
  · contradiction
  · rename_i heq _
    split at heq
    · rename_i m'' _ _ _ _ m' _ hn' _ _ _
      have : 0 ≤ -[m'' +1] := by
        rw [← Int.ofNat_inj.mp hn'] at heq
        have : 0 ≤ Int.ofNat m' - Int.ofNat (m' / 1460) + Int.ofNat (m' / 36524) := hzero
        rwa [heq] at this
      have := Int.negSucc_lt_zero m''
      omega
    · contradiction
    · contradiction
    · contradiction
  · contradiction

theorem yoe_le_of_doe_eq_146096 {doe yoe : Int} (hdoe : doe = 146096)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : yoe = 399 := by
  simp_all
  rfl

theorem yoe_le {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 146096)
  (hyoe : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
    : 0 ≤ yoe ∧ yoe ≤ 399 := by
  if h : doe ≤ 1459
  then
    have := @yoe_le_of_doe_lt_1460 doe yoe (by omega) hyoe
    omega
  else if h : doe ≤ 36523
  then
    have := @yoe_le_of_doe_lt_36524 doe yoe (by omega) hyoe
    omega
  else if h : doe < 146096
  then
    exact @yoe_le_of_doe_lt_146096 doe yoe (by omega) hyoe
  else
    have := @yoe_le_of_doe_eq_146096 doe yoe (by omega) hyoe
    omega

/-- Is leap year of year of era `yoe` starting at 0
-/
def isLeapOfYearOfEra (yoe : Nat) : Bool :=
  (yoe + 1) % 4 = 0 ∧ ((yoe + 1) % 100 ≠ 0 ∨ (yoe + 1) % 400 = 0)

theorem doe_eq_364_sub_0 (k n : Nat) (h : n ≤ k - 2) (hk : 2 ≤ k ∧ k < 25)
  (hdoe : doe = k * 1460 + (k - 2) - n - (365 * ((k * 1460 + (k - 2) - n - k) / 365)
                + (k * 1460 + (k - 2) - n - k) / 365 / 4))
    : doe = 364 - n := by
  rw  [hdoe]
  have : (k * 1460 + (k - 2) - n - k) = (k * 1460 - n - 2) := by omega
  rw [this]
  have : 365 * ((k * 1460 - n - 2) / 365) = k * 1460 - n - 2 - 363 + n := by omega
  rw [this]
  omega

theorem doy_of_doe_eq_365_0 {doe yoe doy : Nat} (hle1 : 0 ≤ doe ∧ doe < 36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365)
  (hyoe : yoe = (doe - doe / 1460) / 365) (hdoy : doy = doe - (365 * yoe + yoe / 4))
    : doe % 1461 = 1460 ↔ doy = 365 :=
  Iff.intro
    (fun h => by omega)
    (fun h => by
      generalize hk : doe / 1460 = k at h
      have : k < 25 := by omega
      if doe = k * 1460 + (k - 1)
      then omega
      else
          have ⟨n, hn⟩ : ∃ (n : Nat), n ≤ k - 2 ∧ doe = k * 1460 + (k - 2) - n := by
            have ⟨n', hn'⟩ := @Nat.exists_eq_add_of_le' doe.succ (k * 1460 + (k - 1)) (by omega)
            exact ⟨n', by omega⟩
          have : doy = 364 - n := by
            rw [hdoy, hyoe, hk, hn.right]
            exact doe_eq_364_sub_0 k n hn.left (by omega) rfl
          omega)

theorem doy_of_doe_lt_365_0 {doe yoe doy : Nat} (hle1 : 0 ≤ doe ∧ doe < 36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365)
  (hyoe : yoe = (doe - doe / 1460) / 365) (hdoy : doy = doe - (365 * yoe + yoe / 4))
  (hlt : doe % 1461 < 1460)
    : doy < 365 := by
  have := doy_of_doe_eq_365_0 hle1 hle2 hyoe hdoy
  omega

theorem not_isLeapOfYearOfEra {yoe : Nat} (h : ¬isLeapOfYearOfEra yoe)
    : ¬ (yoe + 1) % 4 = 0 || ((yoe + 1) % 100 = 0 ∧  ¬ (yoe + 1) % 400 = 0) := by
  unfold isLeapOfYearOfEra at h
  simp_all
  exact Decidable.not_or_of_imp h

theorem doe_of_mod_lt_0 {doe yoe : Nat} (h : 0 ≤ doe ∧ doe < 36524)
  (hyoe : yoe = (doe - doe / 1460) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 < 1460 := by
  have := not_isLeapOfYearOfEra hNot
  simp_all
  generalize hk : doe / 1460 = k at h
  if doe = k * 1460 + (k - 1)
  then omega
  else omega

theorem doe_eq_364_sub_1 (k n : Nat) (h : n ≤ k - 3) (hk : 25 ≤ k ∧ k < 49)
  (hdoe : doe = k * 1460 + (k - 3) - n - (365 * ((k * 1460 + (k - 3) - n - k + 1) / 365)
                + (k * 1460 + (k - 3) - n - k + 1) / 365 / 4 - 1))
    : doe = 364 - n := by
  rw  [hdoe]
  have : (k * 1460 + (k - 3) - n - k + 1) = (k * 1460 - n - 2) := by omega
  rw [this]
  have : 365 * ((k * 1460 - n - 2) / 365) = k * 1460 - n - 2 - 363 + n := by omega
  rw [this]
  omega

theorem doy_of_doe_eq_365_1 {doe yoe doy : Nat} (hle1 : 36524 ≤ doe ∧ doe < 2*36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + 1) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - 1))
    : doe % 1461 + 1 = 1460 ↔ doy = 365 :=
  Iff.intro
    (fun h => by omega)
    (fun h => by
      generalize hk : doe / 1460 = k at h
      have : 25 ≤ k := by omega
      have : k < 50 := by omega
      if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2)
      then omega
      else
        have ⟨n, hn⟩ : ∃ (n : Nat), n ≤ k - 3 ∧ doe = k * 1460 + (k - 3) - n := by
          have ⟨n', hn'⟩ := @Nat.exists_eq_add_of_le' doe.succ (k * 1460 + (k - 2)) (by omega)
          exact ⟨n', by omega⟩
        have : doy = 364 - n := by
          rw [hdoy, hyoe, hk, hn.right]
          exact doe_eq_364_sub_1 k n hn.left (by omega) rfl
        omega)

theorem doe_eq_364_sub_2 (k n : Nat) (h : n ≤ k - 4) (hk : 50 ≤ k ∧ k < 75)
  (hdoe : doe = k * 1460 + (k - 4) - n - (365 * ((k * 1460 + (k - 4) - n - k + 2) / 365)
                + (k * 1460 + (k - 4) - n - k + 2) / 365 / 4 - 2))
    : doe = 364 - n := by
  rw  [hdoe]
  have : (k * 1460 + (k - 4) - n - k + 2) = (k * 1460 - n - 2) := by omega
  rw [this]
  have : 365 * ((k * 1460 - n - 2) / 365) = k * 1460 - n - 2 - 363 + n := by omega
  rw [this]
  omega

theorem doy_of_doe_eq_365_2 {doe yoe doy : Nat} (hle1 : 2*36524 ≤ doe ∧ doe < 3*36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + 2) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - 2))
    : doe % 1461 + 2 = 1460 ↔ doy = 365 :=
  Iff.intro
    (fun h => by omega)
    (fun h => by
      generalize hk : doe / 1460 = k at h
      have : 50 ≤ k := by omega
      have : k < 75 := by omega
      if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2) ∨ doe = k * 1460 + (k - 3)
      then omega
      else
        have ⟨n, hn⟩ : ∃ (n : Nat), n ≤ k - 4 ∧ doe = k * 1460 + (k - 4) - n := by
          have ⟨n', hn'⟩ := @Nat.exists_eq_add_of_le' doe.succ (k * 1460 + (k - 3)) (by omega)
          exact ⟨n', by omega⟩
        have : doy = 364 - n := by
          rw [hdoy, hyoe, hk, hn.right]
          exact doe_eq_364_sub_2 k n hn.left (by omega) (by omega)
        omega)

theorem doe_eq_364_sub_3 (k n : Nat) (h : n ≤ k - 5) (hk : 75 ≤ k ∧ k < 100)
  (hdoe : doe = k * 1460 + (k - 5) - n - (365 * ((k * 1460 + (k - 5) - n - k + 3) / 365)
                + (k * 1460 + (k - 5) - n - k + 3) / 365 / 4 - 3))
    : doe = 364 - n := by
  rw  [hdoe]
  have : (k * 1460 + (k - 5) - n - k + 3) = (k * 1460 - n - 2) := by omega
  rw [this]
  have : 365 * ((k * 1460 - n - 2) / 365) = k * 1460 - n - 2 - 363 + n := by omega
  rw [this]
  omega

theorem doy_of_doe_eq_365_3 {doe yoe doy : Nat} (hle1 : 3*36524 ≤ doe ∧ doe < 4*36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + 3) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - 3))
    : doe % 1461 + 3 = 1460 ↔ doy = 365 :=
  Iff.intro
    (fun h => by omega)
    (fun h => by
      generalize hk : doe / 1460 = k at h
      have : 75 ≤ k := by omega
      have : k < 100 := by omega
      if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2) ∨ doe = k * 1460 + (k - 3)
          ∨ doe = k * 1460 + (k - 4)
      then omega
      else
        have ⟨n, hn⟩ : ∃ (n : Nat), n ≤ k - 5 ∧ doe = k * 1460 + (k - 5) - n := by
          have ⟨n', hn'⟩ := @Nat.exists_eq_add_of_le' doe.succ (k * 1460 + (k - 4)) (by omega)
          exact ⟨n', by omega⟩
        have : doy = 364 - n := by
          rw [hdoy, hyoe, hk, hn.right]
          exact doe_eq_364_sub_3 k n hn.left (by omega) rfl
        omega)

theorem doy_of_doe_eq_365 {doe yoe doy : Nat} (hle1 : 36524 ≤ doe ∧ doe < 146096)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + doe / 36524) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - yoe / 100))
    : doe % 1461 + doe / 36524 = 1460 ↔ doy = 365 := by
  if h : doe < 2*36524
  then
    have := @doy_of_doe_eq_365_1 doe yoe doy (by omega) hle2 (by omega) (by omega)
    omega
  else if h : doe < 3*36524
  then
    have := @doy_of_doe_eq_365_2 doe yoe doy (by omega) hle2 (by omega) (by omega)
    omega
  else
    have := @doy_of_doe_eq_365_3 doe yoe doy (by omega) hle2 (by omega) (by omega)
    omega

theorem doy_of_doe_lt_365 {doe yoe doy : Nat} (hle1 : 36524 ≤ doe ∧ doe < 146096)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + doe / 36524) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - yoe / 100)) (hne : doe % 1461 + doe / 36524 ≠ 1460)
    : doy < 365 := by
  have himp := doy_of_doe_eq_365 hle1 hle2 hyoe hdoy
  omega

theorem doe_of_mod_lt_1 {doe yoe : Nat} (h : 36524 ≤ doe ∧ doe < 2*36524)
  (hyoe : yoe = (doe - doe / 1460 + 1) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 + 1 ≠ 1460 := by
  have := not_isLeapOfYearOfEra hNot
  simp_all
  generalize hk : doe / 1460 = k at h
  if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2)
  then omega
  else omega

theorem doe_of_mod_lt_2 {doe yoe : Nat} (h : 2*36524 ≤ doe ∧ doe < 3*36524)
  (hyoe : yoe = (doe - doe / 1460 + 2) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 + 2 ≠ 1460 := by
  have := not_isLeapOfYearOfEra hNot
  simp_all
  generalize hk : doe / 1460 = k at h
  if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2) ∨ doe = k * 1460 + (k - 3)
  then omega
  else omega

theorem doe_of_mod_lt_3 {doe yoe : Nat} (h : 3*36524 ≤ doe ∧ doe < 4*36524)
  (hyoe : yoe = (doe - doe / 1460 + 3) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 + 3 ≠ 1460 := by
  have := not_isLeapOfYearOfEra hNot
  simp_all
  generalize hk : doe / 1460 = k at h
  if doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - 2)
      ∨ doe = k * 1460 + (k - 3) ∨ doe = k * 1460 + (k - 4)
  then omega
  else omega

theorem doe_of_mod_lt {doe yoe : Nat} (h : 36524 ≤ doe ∧ doe < 146096)
  (hyoe : yoe = (doe - doe / 1460 + doe / 36524) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 + doe / 36524 ≠ 1460 := by
  if doe < 2*36524 then have := @doe_of_mod_lt_1 doe yoe (by omega) (by omega) hNot; omega
  else if doe < 3*36524 then have := @doe_of_mod_lt_2 doe yoe (by omega) (by omega) hNot; omega
  else have := @doe_of_mod_lt_3 doe yoe (by omega) (by omega) hNot; omega

theorem day_le_of {doy yoe : Int}
  (h : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364))
    : 0 ≤ doy ∧ doy ≤ 365 := by
  split at h <;> omega

theorem doy_le {doe yoe doy : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 146096)
  (hyoe : 0 ≤ yoe ∧ yoe ≤ 399)
  (heq : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365)
  (hdoy : doy = doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100))
    : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364) := by
  simp [Int.tdiv] at hdoy
  split at hdoy
  · rename_i yoe _ hn'
    rw [← Int.ofNat_inj.mp hn'] at hdoy
    match doe with
    | ofNat doe =>
      norm_cast at hdoy
      if doe < 1460
      then
        have : yoe = doe / 365 := ofNat_inj.mp (@yoe_of_doe_lt_1460 doe yoe (by omega) heq)
        have : yoe / 4 = 0 := by omega
        have : yoe / 100 = 0 := by omega
        simp [] at hdoy
        split <;> omega
      else if h : doe < 36524
      then
        have hyd := @yoe_of_doe_lt_36524 doe yoe (by omega) heq
        have : yoe = (doe - doe / 1460) / 365  :=  Int.tdiv_sub_eq_div_sub hyd.left
                  (Int.sub_nonneg_of_le (Int.le_trans hyd.right (by omega)))
        have : yoe / 100 = (0:Int) := by omega
        simp [] at hdoy
        rw [this] at hdoy
        simp [] at hdoy
        have : 0 ≤ doy := by omega
        simp [this]
        have : doy ≤ 365 := by omega
        split
        · simp [this]
        · rename_i h
          have := @doy_of_doe_lt_365_0 doe yoe doy.toNat (by omega) (by omega) (by omega)
                  (by omega) (@doe_of_mod_lt_0 doe yoe (by omega) (by omega) h)
          omega
      else if h : doe < 146096
      then
        have hyd := @yoe_of_doe_lt_146096 doe yoe (by omega) heq
        have hm : yoe = (doe - doe / 1460 + doe / 36524) / 365  :=
                   Int.tdiv_sub_add_eq_div_sub_add hyd.left (by simp [Int.tdiv]; omega)
        have : yoe / 100 = doe / 36524 := by rw [hm, Nat.div_div_eq_div_mul]; omega

        simp [] at hdoy
        have : doy ≤ 365 := by omega
        split
        · omega
        · rename_i h
          have := @doy_of_doe_lt_365 doe yoe doy.toNat (by omega) (by omega) hm
                  (by omega) (@doe_of_mod_lt doe yoe (by omega) hm h)
          omega
      else if h : doe = 146096
      then
        have : yoe = 399 := Int.ofNat_inj.mp (@yoe_le_of_doe_eq_146096 doe yoe (by omega) heq)
        rw [this] at hdoy
        simp [] at hdoy
        have : isLeapOfYearOfEra yoe = true := by simp [isLeapOfYearOfEra, this]
        split
        · omega
        · contradiction
      else
        have : doe ≤ 146096 := Int.ofNat_le.mp hdoe.right
        omega
  · contradiction
  · have := hyoe.left
    contradiction
  · contradiction

theorem mp_of_nat_le {doy mp m : Nat} (hdoy : 0 ≤ ofNat doy ∧ ofNat doy ≤ 365)
  (hmp : mp = m / 153) (heq : 5 * doy + 2 = m)
    : 0 ≤ ofNat mp ∧ ofNat mp ≤ 11 := by
  have : 0 ≤ ofNat mp := Int.ofNat_le.mpr (Nat.zero_le mp)
  have : mp ≤ 11 := by
    rw [← heq] at hmp
    have : doy ≤ 365 := Int.ofNat_le.mp hdoy.right
    omega
  have : ofNat mp ≤ 11 := Int.ofNat_le.mpr this
  simp_all

theorem mp_le {doy mp : Int} (hdoy : 0 ≤ doy ∧ doy ≤ 365) (hmp : mp = month_from_doy doy)
    : 0 ≤ mp ∧ mp ≤ 11 := by
  simp [month_from_doy, Int.tdiv] at hmp
  split at hmp
  · rename_i m' n' heq hn
    rw [← Int.ofNat_inj.mp hn] at hmp
    match doy, mp with
    | ofNat doy, ofNat mp => exact mp_of_nat_le hdoy (Int.ofNat_inj.mp hmp) (Int.ofNat_inj.mp heq)
  · contradiction
  · match doy with | ofNat _ => contradiction
  · contradiction

theorem d_le' {d : Int} {doy mp m' m'' n' n'' : Nat}
  (heq : 153 * (m' / n') + 2 = m'') (hn' : 153 = n') (hm' : 5 * doy + 2 = m')
  (hmp : mp = (5 * doy + 2) / 153) (hle : 0 ≤ mp ∧ mp ≤ 11)
  (hd : d = ofNat doy - ofNat (m'' / n'') + 1) (hn'' : 5 = n'')
    : 1 ≤ d ∧ d ≤ 31 := by
  rw [← hn'] at heq
  rw [← hn''] at hd
  rw [← hm'] at heq

  have hm : m'' = mp * 153 + 2 := by omega

  if h : mp = 0 then simp [hm] at hd; omega
  else if h : mp = 1 then simp [hm] at hd; omega
  else if h : mp = 2 then simp [hm] at hd; omega
  else if h : mp = 3 then simp [hm] at hd; omega
  else if h : mp = 4 then simp [hm] at hd; omega
  else if h : mp = 5 then simp [hm] at hd; omega
  else if h : mp = 6 then simp [hm] at hd; omega
  else if h : mp = 7 then simp [hm] at hd; omega
  else if h : mp = 8 then simp [hm] at hd; omega
  else if h : mp = 9 then simp [hm] at hd; omega
  else if h : mp = 10 then simp [hm] at hd; omega
  else if h : mp = 11 then simp [hm] at hd; omega
  else omega

theorem d_le {doy mp d : Int} (hdoy : 0 ≤ doy ∧ doy ≤ 365) (hle : 0 ≤ mp ∧ mp ≤ 11)
  (hmp : mp = month_from_doy doy) (hd : d = doy - (doy_from_month mp) + 1)
    : 1 ≤ d ∧ d ≤ 31 := by
  rw [hmp] at hd
  simp [doy_from_month, month_from_doy, Int.tdiv] at hd
  split at hd
  · rename_i heq _
    split at heq
    · rename_i m'' n'' hn' _ _ m' n' heq' hn
      match doy, mp with
      | ofNat doy, ofNat mp =>
        exact @d_le' d doy mp m' m'' n' n'' (Int.ofNat_inj.mp heq)
                      (Int.ofNat_inj.mp hn) (Int.ofNat_inj.mp heq')
                      (month_from_doy_of_nat_eq doy mp hmp.symm).symm
                      (And.intro (Int.ofNat_le.mp hle.left) (Int.ofNat_le.mp hle.right))
                      hd (Int.ofNat_inj.mp hn')
    · contradiction
    · match doy with | ofNat _ => contradiction
    · contradiction
  · contradiction
  · rename_i heq _
    split at heq
    · contradiction
    · contradiction
    · match doy with | ofNat _ => contradiction
    · contradiction
  · contradiction

theorem m_le {mp : Int} (hmp : 0 ≤ mp ∧ mp ≤ 11) (hm : m = mp + (if mp < 10 then 3 else -9))
    : 1 ≤ m ∧ m ≤ 12 := by
  split at hm <;> simp_all <;> omega

def month_to_mp (m : Month.Ordinal) :=
  if m.val < 3 then m.val + 9 else m.val - 3

def mp_to_month (mp : Int ) (hmp : 0 ≤ mp ∧ mp ≤ 11) : Month.Ordinal :=
  let month := mp + (if mp < 10 then 3 else -9)
  have : month = mp + (if mp < 10 then 3 else -9) := rfl
  ⟨month, by rw [this]; exact m_le hmp this⟩

theorem mp_to_month_of_mp_to_month_eq_id (mp : Int ) (hmp : 0 ≤ mp ∧ mp ≤ 11)
    : month_to_mp (mp_to_month mp hmp) = mp := by
  simp [month_to_mp, mp_to_month]
  split <;> omega

protected theorem Array.get_eq_get_of_eq (a : Array α) (n m : Nat) (hn) (hm) (h : n = m)
    : a[n]'hn = a[m]'hm := getElem_congr h

namespace Notation

declare_syntax_cat DaysEqDaysOfMp
syntax num ws num ws num : DaysEqDaysOfMp
syntax "daysEqDaysOfMp%" DaysEqDaysOfMp : term

macro_rules
| `(daysEqDaysOfMp% $m:num $mp:num $len:num) =>
    `((fun leapOfYear leapOfYearOfEra mp hm hmp => by
    rw [Subtype.ext_iff]
    simp []
    have h : mp.toNat = $mp := by omega
    have h1 : $mp < (monthSizes leapOfYearOfEra).val.size := by
      simp [(monthSizes leapOfYearOfEra).property]
    have h2 : mp.toNat < (monthSizes leapOfYearOfEra).val.size := by
      simp [(monthSizes leapOfYearOfEra).property, h]
    rw [Array.get_eq_get_of_eq (monthSizes leapOfYearOfEra).val mp.toNat $mp h2 h1 h]

    have h1 : (monthSizes leapOfYearOfEra).val[$mp]'h1 = $len := rfl
    have h2 : (Month.Ordinal.days leapOfYear ⟨$m, by omega⟩).val = $len := rfl
    rwa [h1, h2]
    : ∀ (leapOfYear leapOfYearOfEra : Bool) (mp : Int)
        (hm : $m = mp + if mp < 10 then 3 else -9) (hmp : 0 ≤ mp ∧ mp ≤ 11),
          Month.Ordinal.days leapOfYear ⟨$m, by omega⟩
          = ⟨(monthSizes leapOfYearOfEra).val.get mp.toNat
              (by rw [(monthSizes leapOfYearOfEra).property]; omega),
            by
              have := monthSizesLeap_le leapOfYearOfEra mp.toNat (by omega)
              exact And.intro (by simp_all; omega) (by norm_cast; simp_all)⟩
          ))

end Notation

def days_eq_days_of_mp_1 := daysEqDaysOfMp% 1 10 31
def days_eq_days_of_mp_3 := daysEqDaysOfMp% 3 0 31
def days_eq_days_of_mp_4 := daysEqDaysOfMp% 4 1 30
def days_eq_days_of_mp_5 := daysEqDaysOfMp% 5 2 31
def days_eq_days_of_mp_6 := daysEqDaysOfMp% 6 3 30
def days_eq_days_of_mp_7 := daysEqDaysOfMp% 7 4 31
def days_eq_days_of_mp_8 := daysEqDaysOfMp% 8 5 31
def days_eq_days_of_mp_9 := daysEqDaysOfMp% 9 6 30
def days_eq_days_of_mp_10 := daysEqDaysOfMp% 10 7 31
def days_eq_days_of_mp_11 := daysEqDaysOfMp% 11 8 30
def days_eq_days_of_mp_12 := daysEqDaysOfMp% 12 9 31

theorem days_eq_days_of_mp_2 (leapOfYear leapOfYearOfEra  : Bool) (mp : Int)
  (hm : 2 = mp + (if mp < 10 then 3 else -9)) (hmp : 0 ≤ mp ∧ mp ≤ 11)
  (hIsLeap : 10 ≤ mp → leapOfYearOfEra = leapOfYear)
    : Month.Ordinal.days leapOfYear ⟨2, by omega⟩
    = ⟨(monthSizes leapOfYearOfEra).val.get mp.toNat (by rw [(monthSizes leapOfYearOfEra).property]; omega),
        by
          have := monthSizesLeap_le leapOfYearOfEra mp.toNat (by omega)
          exact And.intro (by simp_all; omega) (by norm_cast; simp_all)⟩ := by
  rw [Subtype.ext_iff]
  simp []
  have h : mp.toNat = 11 := by omega
  have h1 : 11 < (monthSizes leapOfYearOfEra).val.size := List.isSome_getElem?.mp rfl
  have h2 : mp.toNat < (monthSizes leapOfYearOfEra).val.size := lt_of_eq_of_lt h h1
  rw [Array.get_eq_get_of_eq (monthSizes leapOfYearOfEra).val mp.toNat 11 h2 h1 h]
  have h1 : (monthSizes leapOfYearOfEra).val[11]'h1 = if leapOfYearOfEra then 29 else 28 := rfl
  have h2 : (Month.Ordinal.days leapOfYear ⟨2, m_le hmp hm⟩).val = if leapOfYear then 29 else 28 := by
    cases leapOfYear <;> rfl
  rw [h1, h2]

  rw [hIsLeap (by omega)]
  cases leapOfYear <;> simp

theorem days_eq_days_of_mp (leapOfYear leapOfYearOfEra : Bool) (month : Month.Ordinal)
  (mp : Int)
  (hm : month.val = mp + (if mp < 10 then 3 else -9))
  (hmp' : 0 ≤ mp ∧ mp ≤ 11)
  (hIsLeap : 10 ≤ mp → leapOfYearOfEra = leapOfYear)
    : Month.Ordinal.days leapOfYear month
    = ⟨(monthSizes leapOfYearOfEra).val.get mp.toNat
          (by rw [(monthSizes leapOfYearOfEra).property]; omega),
        by
          have := monthSizesLeap_le leapOfYearOfEra mp.toNat (by omega)
          exact And.intro (by simp_all; omega) (by norm_cast; simp_all)⟩ := by
  have : month = mp_to_month mp hmp' := by
    simp [mp_to_month]
    rw [Subtype.ext_iff, hm]
  have : mp = month_to_mp month := by
    simp [month_to_mp]
    omega
  have : 1 ≤ month.val := by omega
  have : month.val ≤ 12 := by omega
  match month with
  | ⟨1, _⟩ => exact days_eq_days_of_mp_1 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨2, _⟩ => exact days_eq_days_of_mp_2 leapOfYear leapOfYearOfEra mp hm hmp' hIsLeap
  | ⟨3, _⟩ => exact days_eq_days_of_mp_3 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨4, _⟩ => exact days_eq_days_of_mp_4 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨5, _⟩ => exact days_eq_days_of_mp_5 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨6, _⟩ => exact days_eq_days_of_mp_6 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨7, _⟩ => exact days_eq_days_of_mp_7 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨8, _⟩ => exact days_eq_days_of_mp_8 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨9, _⟩ => exact days_eq_days_of_mp_9 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨10, _⟩ => exact days_eq_days_of_mp_10 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨11, _⟩ => exact days_eq_days_of_mp_11 leapOfYear leapOfYearOfEra mp hm hmp'
  | ⟨12, _⟩ => exact days_eq_days_of_mp_12 leapOfYear leapOfYearOfEra mp hm hmp'

theorem doy_from_month_le (n m day : Nat) (heq : 5 * day + 2 = m) (h : n = m / 153)
    : doy_from_month n ≤ day := by
  simp [doy_from_month, Int.tdiv]
  split
  · rename_i m' n' heq' hn
    norm_cast
    simp [← Int.ofNat.inj hn]
    have : 153 * n + 2 = m' := Int.ofNat.inj heq'
    omega
  · contradiction
  · contradiction
  · contradiction

theorem doy_from_next_month_le (n m day : Nat) (heq : 5 * day + 2 = m) (h : n = m / 153)
    : day ≤ doy_from_month (n+1) - 1 := by
  simp [doy_from_month, Int.tdiv]
  split
  · rename_i m' n' heq' hn
    norm_cast
    simp [← Int.ofNat.inj hn]
    have : 153 * (n+1) + 2 = m' := by simp [Int.ofNat.inj heq']
    omega
  · contradiction
  · contradiction
  · contradiction

theorem month_from_doy_le (n : Nat) (doy : Int) (h : n = month_from_doy doy)
  (hdoy : 0 ≤ doy) : doy_from_month n ≤ doy ∧ doy ≤ doy_from_month (n+1) - 1 := by
  simp [month_from_doy, Int.tdiv] at h
  have : ¬5 * doy + 2 < 0 := by omega
  split at h
  · rename_i m' n' heq _
    match h : doy with
    | ofNat day =>
        rename_i heq' h'
        have hlt : n * 153 ≤ m' ∧ m' < (n+1) * 153 := by
          have h : n = m' / n' := ofNat_inj.mp h'
          simp [← Int.ofNat.inj heq'] at h
          exact @Nat.div_mul_lt m' 153 n (by simp) (by omega)
        simp
        have heq : 5 * day + 2 = m' := Int.ofNat.inj heq
        rw [← heq] at hlt
        exact And.intro
          (doy_from_month_le n m' day heq (by omega))
          (doy_from_next_month_le n m' day heq (by omega))
    | negSucc _ => contradiction
  · contradiction
  · rename_i heq _
    have : 5 * doy + 2 < 0 := by rw [heq]; exact Int.negSucc_lt_zero _
    contradiction
  · contradiction

theorem doy_sub_le (mp doy : Int) (leap : Bool) (hmp : mp = month_from_doy doy)
  (hmp' : 0 ≤ mp ∧ mp ≤ 11) (hdoy : 0 ≤ doy ∧ doy ≤ (if leap then 365 else 364))
    : doy - doy_from_month mp + 1 ≤ (monthSizes leap).val.get mp.toNat
        (by rw [(monthSizes leap).property]; omega) := by
  simp
  have : 0 ≤ month_from_doy doy := by omega
  have hlt := month_from_doy_le mp.toNat doy (by simp_all [hmp]; omega) hdoy.left
  have hn : mp = (mp.toNat:Int) := by omega
  have := monthSizesLeap_eq_doy_from_month_sub leap (mp.toNat) (by omega)
  split at this
  · rw [this]
    rw [← hn]
    have : doy + 1 ≤ doy_from_month (mp + 1) := by
      rw [← hn] at hlt
      omega
    omega
  · rw [this]
    rw [← hn]
    cases leap
    · have : doy + 1 ≤ 365 := by simp [] at hdoy; omega
      omega
    · have : doy + 1 ≤ 366 := by omega
      simp
      omega

/--
Proof that the date `(year, month, day)` of `ofDaysSinceUNIXEpoch'` is valid.
-/
theorem ofDaysSinceUNIXEpochIsValid (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal)
  (mp doy : Int) (isLeapOfYearOfEra : Bool)
  (hmp : mp = month_from_doy doy)
  (hm : month.val = mp + (if mp < 10 then 3 else -9))
  (hd : day.val = doy - (doy_from_month mp) + 1)
  (hdoy : 0 ≤ doy ∧ (if isLeapOfYearOfEra then doy ≤ 365 else doy ≤ 364))
  (hmp' : 0 ≤ mp ∧ mp ≤ 11)
  (hIsLeap : 10 ≤ mp → isLeapOfYearOfEra = year.isLeap)
    : day ≤ month.days year.isLeap := by
  rw [days_eq_days_of_mp year.isLeap isLeapOfYearOfEra month mp hm hmp' hIsLeap]
  have hp := day.property
  have : day = ⟨doy - (doy_from_month mp) + 1, And.intro (by omega) (by omega)⟩ := by
    rw [Subtype.ext_iff]
    exact hd
  rw [this]
  have := doy_sub_le mp doy isLeapOfYearOfEra hmp hmp' (by split at hdoy <;> simp_all)
  norm_cast

theorem mod_4_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 4 = 0 ↔ (yoe + 1 + era * 400).tmod 4 = 0  := by
  have : 4 * (era * 100) = era * 400 := by omega
  rw [← this]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 4 = 0 := by exact natAbs_eq_zero.mp h
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*100) 4).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*100) 4).mpr h
      exact ofNat_eq_zero.mp this)

theorem mod_100_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 100 = 0 ↔ (yoe + 1 + era * 400).tmod 100 = 0  := by
  have : 100 * (era * 4) = era * 400 := by omega
  rw [← this]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 100 = 0 := natAbs_eq_zero.mp h
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*4) 100).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*4) 100).mpr h
      have h : (yoe + 1) % 100 = 0 := ofNat_eq_zero.mp this
      exact h)

theorem mod_400_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 400 = 0 ↔ (yoe + 1 + era * 400).tmod 400 = 0  := by
  rw [Int.mul_comm]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 400 = 0 := by have := ofNat_tmod (yoe+1) 400; simp_all
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) era 400).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) era 400).mpr h
      have h : (yoe + 1) % 400 = 0 := by have := ofNat_tmod (yoe+1) 400; simp_all; omega
      exact h)

def isLeapOfYearOfEras (yoe : Nat) (era : Int) : Bool :=
  (yoe + era * 400 + 1).tmod 4 = 0
  ∧ ((yoe + era * 400 + 1).tmod 100 ≠ 0 ∨ (yoe + era * 400 + 1).tmod 400 = 0)

theorem isLeapOfYearOfEras_eq (era yoe : Int)
    : isLeapOfYearOfEra yoe.toNat = isLeapOfYearOfEras yoe.toNat era := by
  unfold isLeapOfYearOfEra isLeapOfYearOfEras

  have := mod_4_zero_of_add_iff era yoe.toNat
  have : (yoe.toNat + 1) % 100 ≠ 0 ↔ (↑yoe.toNat + 1 + era * 400).tmod 100 ≠ 0 := by
    have := mod_100_zero_of_add_iff era yoe.toNat
    exact not_congr this
  have := mod_400_zero_of_add_iff era yoe.toNat
  simp_all
  have : max yoe 0 + 1 + era * 400 = max yoe 0 + era * 400 + 1 := by omega
  rw [this]

theorem is_leap_of_year_of_era_eq_is_leap_of_year (era yoe mp y' y : Int)
  (hyoe : 0 ≤ yoe ∧ yoe ≤ 399) (hy' : y' = yoe + era * 400)
  (hy : y = y' + (if 10 ≤ mp then 1 else 0))
    : 10 ≤ mp → isLeapOfYearOfEra yoe.toNat = (Year.Offset.ofInt y).isLeap := by
  intro
  rename_i h
  have hy : y = y' + 1 := by
    split at hy
    · exact hy
    · contradiction
  have heq : (Year.Offset.ofInt y).toInt = y := rfl
  have hmax : max yoe 0 = yoe := by omega
  rw [isLeapOfYearOfEras_eq era yoe]

  simp [isLeapOfYearOfEras, Year.Offset.isLeap]
  rw [heq, hy, hy', hmax]

private theorem m_to_mp (m mp y y' : Int) (hm : y = y' + (if m <= 2 then 1 else 0))
  (hle : 0 ≤ mp ∧ mp ≤ 11) (hmp : m = mp + (if mp < 10 then 3 else -9))
    : y = y' + if 10 ≤ mp then 1 else 0 := by
  have : y' + (if m <= 2 then 1 else 0) = y' + (if 10 ≤ mp then 1 else 0) := by  omega
  rwa [this] at hm

/--
Create a date from the number of days since the UNIX epoch (January 1st, 1970)
and prove that the date is a valid `PlainDate`,
see
* https://github.com/leanprover/lean4/blob/v4.15.0-rc1/src/Std/Time/Date/PlainDate.lean#L79
* http://howardhinnant.github.io/date_algorithms.html#civil_from_days
-/
def ofDaysSinceUNIXEpoch' (day : Day.Offset) : PlainDate :=
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
  let doe := z - era * 146097
  have hdoe : 0 ≤ doe ∧ doe ≤ 146096 := doe_le z era doe rfl rfl
  let yoe := (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365
  have hyoe : 0 ≤ yoe ∧ yoe ≤ 399 := yoe_le hdoe rfl
  let y' := yoe + era * 400
  let doy := doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100)
  have hdoy : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364) :=
    doy_le hdoe hyoe rfl rfl
  let mp := month_from_doy doy
  have hmp : 0 ≤ mp ∧ mp ≤ 11 := mp_le (day_le_of hdoy) rfl
  let d := doy - (doy_from_month mp) + 1
  have hd : 1 ≤ d ∧ d ≤ 31 := d_le (day_le_of hdoy) hmp rfl rfl
  let m := mp + (if mp < 10 then 3 else -9)
  have hm : 1 ≤ m ∧ m ≤ 12 := m_le hmp rfl
  let y := y' + (if m <= 2 then 1 else 0)
  ⟨y, ⟨m, hm⟩, ⟨d, hd⟩,
    ofDaysSinceUNIXEpochIsValid y ⟨m, hm⟩ ⟨d, hd⟩ mp doy (isLeapOfYearOfEra yoe.toNat)
      rfl rfl rfl hdoy hmp
      (is_leap_of_year_of_era_eq_is_leap_of_year era yoe mp y' y hyoe
          rfl (m_to_mp m mp y y' rfl hmp rfl))⟩

example : PlainDate.ofDaysSinceUNIXEpoch (-719468) =  ⟨0, 3, 1, by decide⟩ := rfl
example : ofDaysSinceUNIXEpoch' (-719468) =  ⟨0, 3, 1, by decide⟩ := rfl
