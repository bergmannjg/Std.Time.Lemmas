import Std.Time.Date.PlainDate
import Std.Time.Date.Unit.Year

import Time.Data.Nat.Lemmas
import Time.Data.Int.Lemmas

/-!
# Additional Time lemmas.

main theorem:

* `Std.Time.Verification.isValid`: proof that the date of `Std.Time.ofDaysSinceUNIXEpoch'` is valid.

-/

namespace Std
namespace Time
namespace Verification

open Std.Time

/-- monthSizes of year starting at month 1, see `Time.Month.Ordinal`. -/
def ordinalMonthSizes (leap : Bool) : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[31, if leap then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31], rfl⟩

def toIndex (month : Time.Month.Ordinal) : Fin ((ordinalMonthSizes leap).val.size) :=
  (month.sub 1).toFin (Int.le_refl 0)

theorem ordinalMonthSizes_eq_days (leap : Bool)
    : ∀ month : Time.Month.Ordinal,
      (ordinalMonthSizes leap).val[toIndex month] = Month.Ordinal.days leap month := by
  intro month
  match month with
  | ⟨m, _⟩ =>
    simp [toIndex, ordinalMonthSizes, Month.Ordinal.days]
    match m with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => split <;> rfl

/-- monthSizes of year starting at month 3 -/
def monthSizes (leap : Bool) : { val : Array Nat // val.size = 12 } :=
  ⟨#[31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, if leap then 29 else 28], rfl⟩

/-- day of year of first day of month, starting at month 3 -/
def doy_from_month (mp : Int) : Int := (153 * mp + 2).tdiv  5

/-- month from day of year, starting at month 3 -/
def month_from_doy (doy : Int) : Int :=  (5 * doy + 2).tdiv 153

/-- Year of era from days of era.  -/
def yoe_from_doe (doe : Int) :=
  (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365

/-- month from month, starting at  3 -/
def month_from_shifted_month (mp : Int) :=
  mp + if mp < 10 then 3 else -9

theorem month_from_shifted_month_le {mp : Int} (hmp : 0 ≤ mp ∧ mp ≤ 11)
    : 1 ≤ month_from_shifted_month mp ∧ month_from_shifted_month mp ≤ 12 := by
  simp [month_from_shifted_month]
  omega

theorem m_le {mp : Int} (hmp : 0 ≤ mp ∧ mp ≤ 11) (hm : m = month_from_shifted_month mp)
    : 1 ≤ m ∧ m ≤ 12 := by
  simp [month_from_shifted_month] at hm
  omega

theorem to_index_from_shifted_eq (leap : Bool) (mp : Int) (month : Time.Month.Ordinal)
  (h : 0 ≤ mp ∧ mp ≤ 11)
  (hm : month.val = month_from_shifted_month mp)
    : toIndex month
    = (⟨(month_from_shifted_month mp - 1).toNat, by
          have := m_le h hm
          have := (ordinalMonthSizes leap).property
          omega⟩ : Fin ((ordinalMonthSizes leap).val.size))  := by
  simp [toIndex, month_from_shifted_month, hm]
  split <;> omega

theorem monthSizes_eq_ordinalMonthSizes (leapOfYear leapOfYearOfEra : Bool)
    : ∀ i : Fin ((monthSizes leapOfYearOfEra).val.size),
      i.val < 11 →
      (monthSizes leapOfYearOfEra).val[i]
      = ((ordinalMonthSizes leapOfYear).val[(month_from_shifted_month i - 1).toNat]'(by
          have := (monthSizes leapOfYearOfEra).property
          have := @month_from_shifted_month_le i.val (by omega)
          have := (ordinalMonthSizes leapOfYear).property
          omega)).val := by
  intro i h
  simp [month_from_shifted_month, ordinalMonthSizes, monthSizes]
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩
  | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ => split <;> rfl

theorem month_from_doy_of_nat_eq (doy mp : Nat)
  (heq : month_from_doy (Int.ofNat doy) = Int.ofNat mp)
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
  cases leap <;> simp +arith +decide [monthSizes, doy_from_month]

theorem monthSizesLeap_le (leap : Bool)
    : ∀ (n : Nat) (h : n ≤ 11),
        28 ≤ (monthSizes leap).val[n]'(by exact Nat.lt_add_one_of_le h)
        ∧ (monthSizes leap).val[n]'(Nat.lt_add_one_of_le h) ≤ 31 := by
  cases leap <;> simp +arith +decide [monthSizes, doy_from_month]

theorem doe_le (z era doe : Int)
  (hera : era = (if z ≥ 0 then z else z - 146096).tdiv 146097) (hdoe : doe = z - era * 146097)
    : 0 ≤ doe ∧ doe ≤ 146096 := by
  simp [hdoe, hera]
  split
  · rename_i h
    rw [Int.sub_tdiv_eq_tmod]
    have := @Int.tmod_lt_of_pos z 146097 (by simp)
    have : z.tmod 146097 ≤ 146096 := Int.lt_add_one_iff.mp this
    simp [this]
    exact Int.tmod_nonneg 146097 h
  · rename_i h
    have : (z - 146096).tdiv 146097 * 146097 ≤ z := Int.sub_tdiv_mul_le z 146097
              (Int.lt_of_not_ge h) (by omega)
    have : z - 146096 ≤ (z - 146096).tdiv 146097 * 146097 := Int.le_sub_tdiv_mul z 146097
              (Int.lt_of_not_ge h) (by omega)
    omega

theorem yoe_of_doe_lt_1460 {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 1459)
  (hyoe : yoe = yoe_from_doe doe)
    : yoe = doe.tdiv 365 := by
  simp [yoe_from_doe] at hyoe
  have : doe.tdiv 1460 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 36524 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt hdoe.left (by omega)
  simp_all

theorem yoe_le_of_doe_lt_1460 {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 1459)
  (hyoe : yoe = yoe_from_doe doe)
    : 0 ≤ yoe ∧ yoe ≤ 3 := by
  have := yoe_of_doe_lt_1460 hdoe hyoe
  have : 0 ≤ doe.tdiv 365 := @Int.tdiv_nonneg doe 365 hdoe.left (Int.le.intro_sub (365 + 0) rfl)
  have : doe.tdiv 365 ≤ 3 := by
    simp [Int.tdiv]
    split <;> simp_all
    rename_i n heq _
    have heq : 365 = n := by omega
    rw [← heq]
    omega
  omega

theorem yoe_of_doe_lt_36524  {doe yoe : Int} (hdoe : 1460 ≤ doe ∧ doe ≤ 36523)
  (hyoe : yoe = yoe_from_doe doe)
    : yoe = (doe - doe.tdiv 1460).tdiv 365 ∧  doe.tdiv 1460 ≤ 25 := by
  simp [yoe_from_doe] at hyoe
  have hle : 0 ≤ doe := by omega
  have : doe.tdiv 1460 ≤ 25 := by
    unfold Int.tdiv
    split <;> simp_all
    rename_i m n heq
    have heq : 1460 = n := by omega
    rw [← heq]
    omega
  have : doe.tdiv 36524 = 0 := Int.tdiv_eq_zero_of_lt hle (by omega)
  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt hle (by omega)
  simp_all

theorem yoe_le_of_doe_lt_36524  {doe yoe : Int} (hdoe : 1460 ≤ doe ∧ doe ≤ 36523)
  (hyoe : yoe = yoe_from_doe doe)
    : 0 ≤ yoe ∧ yoe ≤ 99 := by
  have : 0 ≤ doe := by omega
  have := yoe_of_doe_lt_36524 hdoe hyoe
  have : 0 ≤ (doe - doe.tdiv 1460).tdiv 365 :=
    @Int.tdiv_nonneg (doe - doe.tdiv 1460) 365 (by omega) (Int.le.intro_sub (365 + 0) rfl)
  have : (doe - doe.tdiv 1460).tdiv 365 ≤ 99 := by
    unfold Int.tdiv
    split <;> simp_all
    rename_i heq' heq
    split at heq' <;> simp_all
    rename_i n _ _ _ _ _ _
    have heq : 365 = n := by omega
    rw [← heq]
    rename_i n' hn' _
    have hn' : 1460 = n' := by omega
    rw [← hn'] at heq'
    omega
  omega

theorem yoe_of_doe_lt_146096 {doe yoe : Int} (hdoe : 36524 ≤ doe ∧ doe ≤ 146095)
  (hyoe : yoe = yoe_from_doe doe)
    : yoe = (doe - doe.tdiv 1460 + doe.tdiv 36524).tdiv 365
      ∧ 25 ≤ doe.tdiv 1460
      ∧ doe.tdiv 1460 ≤ 100
      ∧ doe.tdiv 36524 ≤ 3 := by
  simp [yoe_from_doe] at hyoe
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
  (hyoe : yoe = yoe_from_doe doe)
    : 0 ≤ yoe ∧ yoe ≤ 399 := by
  simp [yoe_from_doe] at hyoe
  have : 0 ≤ doe := by omega
  have hlt : doe < 146096 := by omega

  have : doe.tdiv 146096 = 0 := Int.tdiv_eq_zero_of_lt this hlt
  have := yoe_of_doe_lt_146096 hdoe hyoe

  have hzero : 0 ≤ doe - doe.tdiv 1460 + doe.tdiv 36524 := by
    have : 0 ≤ doe.tdiv 36524 := by match doe with | Int.ofNat _ => exact Int.tdiv_of_nat_le
    omega
  have : 0 ≤ (doe - doe.tdiv 1460 + doe.tdiv 36524).tdiv 365 :=
      @Int.tdiv_nonneg (doe - doe.tdiv 1460 + doe.tdiv 36524) 365 hzero (Int.le.intro_sub (365 + 0) rfl)
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
      have : 0 ≤ Int.negSucc m'' := by
        rw [← Int.ofNat_inj.mp hn'] at heq
        have : 0 ≤ Int.ofNat m' - Int.ofNat (m' / 1460) + Int.ofNat (m' / 36524) := hzero
        rwa [heq] at this
      omega
    · contradiction
    · contradiction
    · contradiction
  · contradiction

theorem yoe_le_of_doe_eq_146096 {doe yoe : Int} (hdoe : doe = 146096)
  (hyoe : yoe = yoe_from_doe doe)
    : yoe = 399 := by
  simp_all
  rfl

theorem yoe_le {doe yoe : Int} (hdoe : 0 ≤ doe ∧ doe ≤ 146096)
  (hyoe : yoe = yoe_from_doe doe)
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

theorem doyEq364Sub (i i1 i2 : Nat) (doy k n : Nat)
  (h : n ≤ k - 2 - i)
  (hk :  i1 ≤ k ∧ k < i2)
  (hdoy : doy = k * 1460 + (k - 2 - i) - n
                - (365 * ((k * 1460 + (k - 2 - i) - n - k + i) / 365)
                  + (k * 1460 + (k - 2 - i) - n - k + i) / 365 / 4 - i))
    : (i = 0 ∧ i1 = 2 ∧ i2 = 25
       ∨ i = 1 ∧ i1 = 25 ∧ i2 = 50
       ∨ i = 2 ∧ i1 = 50 ∧ i2 = 75
       ∨ i = 3 ∧ i1 = 75 ∧ i2 = 100) →
      doy = 364 - n := by
  intro hi
  have : (k * 1460 + (k - 2 - i) - n - k + i) = (k * 1460 - n - 2) := by omega
  omega

theorem doyOfDoeEq (i i1 i2 : Nat) (doe yoe doy : Nat)
  (hle1 : i * 36524 ≤ doe ∧ doe < (i + 1) * 36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365)
  (hyoe : yoe = (doe - doe / 1460 + i) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - i))
    : (i = 0 ∧ i1 = 2 ∧ i2 = 25
       ∨ i = 1 ∧ i1 = 25 ∧ i2 = 50
       ∨ i = 2 ∧ i1 = 50 ∧ i2 = 75
       ∨ i = 3 ∧ i1 = 75 ∧ i2 = 100) →
      (doe % 1461 + i = 1460 ↔ doy = 365) := by
  intro hi
  rcases hi with hi | hi | hi | hi
  <;> exact Iff.intro
        (fun h => by omega)
        (fun h => by
          generalize hk : doe / 1460 = k at h
          let n1 := if i = 0 then 1 else 2
          let n2 := if i = 0 then 1 else if i = 1 then 2 else 3
          let n3 := if i = 0 then 1 else if i = 1 then 2 else if i = 1 then 3 else 4
          if h : doe = k * 1460 + (k - 1) ∨ doe = k * 1460 + (k - n1) ∨ doe = k * 1460 + (k - n2)
              ∨ doe = k * 1460 + (k - n3)
          then
            simp [n1, n2, n3, hi] at h
            omega
          else
            simp [n1, n2, n3, hi] at h
            have ⟨n, hn⟩ : ∃ (n : Nat), n ≤ k - 2 - i ∧ doe = k * 1460 + (k - 2 - i) - n := by
              have ⟨n', hn'⟩ := @Nat.exists_eq_add_of_le' doe.succ (k * 1460 + (k - 1 - i)) (by omega)
              exact ⟨n', by omega⟩
            have : doy = 364 - n := by
              rw [hyoe, hk, hn.right] at hdoy
              exact doyEq364Sub i i1 i2 doy k n hn.left (by omega) hdoy (by omega)
            omega)

theorem doy_of_doe_lt_365_0 {doe yoe doy : Nat} (hle1 : 0 ≤ doe ∧ doe < 36524)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365)
  (hyoe : yoe = (doe - doe / 1460) / 365) (hdoy : doy = doe - (365 * yoe + yoe / 4))
  (hlt : doe % 1461 < 1460)
    : doy < 365 := by
  have := doyOfDoeEq 0 2 25 doe yoe doy hle1 hle2 hyoe hdoy (by simp)
  omega

theorem not_isLeapOfYearOfEra {yoe : Nat} (h : ¬isLeapOfYearOfEra yoe)
    : ¬ (yoe + 1) % 4 = 0 || ((yoe + 1) % 100 = 0 ∧  ¬ (yoe + 1) % 400 = 0) := by
  unfold isLeapOfYearOfEra at h
  simp_all
  exact Decidable.not_or_of_imp h

theorem doy_of_doe_eq_365 {doe yoe doy : Nat} (hle1 : 36524 ≤ doe ∧ doe < 146096)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + doe / 36524) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - yoe / 100))
    : doe % 1461 + doe / 36524 = 1460 ↔ doy = 365 := by
  if h : doe < 2*36524
  then
    have :=  doyOfDoeEq 1 25 50 doe yoe doy (by omega) hle2 (by omega) (by omega) (by simp)
    omega
  else if h : doe < 3*36524
  then
    have := doyOfDoeEq 2 50 75 doe yoe doy (by omega) hle2 (by omega) (by omega) (by simp)
    omega
  else
    have := doyOfDoeEq 3 75 100 doe yoe doy (by omega) hle2 (by omega) (by omega) (by simp)
    omega

theorem doy_of_doe_lt_365 {doe yoe doy : Nat} (hle1 : 36524 ≤ doe ∧ doe < 146096)
  (hle2 : 0 ≤ doy ∧ doy ≤ 365) (hyoe : yoe = (doe - doe / 1460 + doe / 36524) / 365)
  (hdoy : doy = doe - (365 * yoe + yoe / 4 - yoe / 100)) (hne : doe % 1461 + doe / 36524 ≠ 1460)
    : doy < 365 := by
  have himp := doy_of_doe_eq_365 hle1 hle2 hyoe hdoy
  omega

theorem doe_of_mod_lt_0 {doe yoe : Nat} (h : 0 ≤ doe ∧ doe < 36524)
  (hyoe : yoe = (doe - doe / 1460) / 365) (hNot : ¬isLeapOfYearOfEra yoe)
    : doe % 1461 < 1460 := by
  have := not_isLeapOfYearOfEra hNot
  simp_all
  generalize hk : doe / 1460 = k at h
  if doe = k * 1460 + (k - 1)
  then omega
  else omega

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
  (heq : yoe = yoe_from_doe doe)
  (hdoy : doy = doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100))
    : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364) := by
  simp [Int.tdiv] at hdoy
  split at hdoy
  · rename_i yoe _ hn'
    rw [← Int.ofNat_inj.mp hn'] at hdoy
    match doe with
    | Int.ofNat doe =>
      if doe < 1460
      then
        have : yoe = doe / 365 := Int.ofNat_inj.mp (@yoe_of_doe_lt_1460 doe yoe (by omega) heq)
        simp only [Int.ofNat_eq_coe] at hdoy
        split <;> omega
      else if h : doe < 36524
      then
        have hyd := @yoe_of_doe_lt_36524 doe yoe (by omega) heq
        have : yoe = (doe - doe / 1460) / 365  :=  Int.tdiv_sub_eq_div_sub hyd.left
                  (Int.sub_nonneg_of_le (Int.le_trans hyd.right (by omega)))
        have : yoe / 100 = 0 := by omega
        simp only [Int.ofNat_eq_coe] at hdoy
        split
        · omega
        · rename_i h
          have := @doy_of_doe_lt_365_0 doe yoe doy.toNat (by omega) (by omega) (by omega)
                  (by omega) (@doe_of_mod_lt_0 doe yoe (by omega) (by omega) h)
          omega
      else if h : doe < 146096
      then
        have hyd := @yoe_of_doe_lt_146096 doe yoe (by omega) heq
        have hm : yoe = (doe - doe / 1460 + doe / 36524) / 365  :=
                   Int.tdiv_sub_add_eq_div_sub_add hyd.left (by simp [Int.tdiv]; omega)
        have : yoe / 100 = doe / 36524 := by omega
        simp only [Int.ofNat_eq_coe] at hdoy
        split
        · omega
        · rename_i h
          have := @doy_of_doe_lt_365 doe yoe doy.toNat (by omega) (by omega) hm
                  (by omega) (@doe_of_mod_lt doe yoe (by omega) hm h)
          omega
      else if h : doe = 146096
      then
        have : yoe = 399 := Int.ofNat_inj.mp (@yoe_le_of_doe_eq_146096 doe yoe (by omega) heq)
        simp only [Int.ofNat_eq_coe] at hdoy
        split
        · omega
        · have : isLeapOfYearOfEra yoe = true := by simp [isLeapOfYearOfEra, this]
          contradiction
      else
        have : doe ≤ 146096 := Int.ofNat_le.mp hdoe.right
        omega
  · contradiction
  · omega
  · contradiction

theorem mp_of_nat_le {doy mp m : Nat} (hdoy : 0 ≤ Int.ofNat doy ∧ Int.ofNat doy ≤ 365)
  (hmp : mp = m / 153) (heq : 5 * doy + 2 = m)
    : 0 ≤ Int.ofNat mp ∧ Int.ofNat mp ≤ 11 := by
  have : mp ≤ 11 := by
    rw [← heq] at hmp
    have : doy ≤ 365 := Int.ofNat_le.mp hdoy.right
    omega
  have : Int.ofNat mp ≤ 11 := Int.ofNat_le.mpr this
  simp_all

theorem mp_le {doy mp : Int} (hdoy : 0 ≤ doy ∧ doy ≤ 365) (hmp : mp = month_from_doy doy)
    : 0 ≤ mp ∧ mp ≤ 11 := by
  simp [month_from_doy, Int.tdiv] at hmp
  split at hmp
  · rename_i m' n' heq hn
    rw [← Int.ofNat_inj.mp hn] at hmp
    match doy, mp with
    | Int.ofNat doy, Int.ofNat mp => exact mp_of_nat_le hdoy (Int.ofNat_inj.mp hmp) (Int.ofNat_inj.mp heq)
  · contradiction
  · omega
  · contradiction

theorem d_le' {d : Int} {doy mp m' m'' n' n'' : Nat}
  (heq : 153 * (m' / n') + 2 = m'') (hn' : 153 = n') (hm' : 5 * doy + 2 = m')
  (hmp : mp = (5 * doy + 2) / 153) (hle : 0 ≤ mp ∧ mp ≤ 11)
  (hd : d = Int.ofNat doy - Int.ofNat (m'' / n'') + 1) (hn'' : 5 = n'')
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
      | Int.ofNat doy, Int.ofNat mp =>
        exact @d_le' d doy mp m' m'' n' n'' (Int.ofNat_inj.mp heq)
                      (Int.ofNat_inj.mp hn) (Int.ofNat_inj.mp heq')
                      (month_from_doy_of_nat_eq doy mp hmp.symm).symm
                      (And.intro (Int.ofNat_le.mp hle.left) (Int.ofNat_le.mp hle.right))
                      hd (Int.ofNat_inj.mp hn')
    · contradiction
    · omega
    · contradiction
  · contradiction
  · rename_i heq _
    split at heq
    · contradiction
    · contradiction
    · omega
    · contradiction
  · contradiction

/-- From month based at january to month based at march. -/
def month_to_mp (m : Month.Ordinal) :=
  if m.val < 3 then m.val + 9 else m.val - 3

/-- From month based at march to month based at january. -/
def mp_to_month (mp : Int ) (hmp : 0 ≤ mp ∧ mp ≤ 11) : Month.Ordinal :=
  ⟨month_from_shifted_month mp, by simp [month_from_shifted_month]; omega⟩

theorem mp_to_month_of_mp_to_month_eq_id (mp : Int ) (hmp : 0 ≤ mp ∧ mp ≤ 11)
    : month_to_mp (mp_to_month mp hmp) = mp := by
  simp [month_to_mp, mp_to_month, month_from_shifted_month]
  omega

protected theorem Array.get_eq_get_of_eq (a : Array α) (n m : Nat) (hn) (hm) (h : n = m)
    : a[n]'hn = a[m]'hm := getElem_congr rfl h hn

theorem days_eq_days_of_mp_2 (leapOfYear leapOfYearOfEra  : Bool) (mp : Int)
  (hm : 2 = month_from_shifted_month mp) (hmp : 0 ≤ mp ∧ mp ≤ 11)
  (hIsLeap : 10 ≤ mp → leapOfYearOfEra = leapOfYear)
    : (Month.Ordinal.days leapOfYear ⟨2, by omega⟩).val
    = (monthSizes leapOfYearOfEra).val[mp.toNat]'
        (by rw [(monthSizes leapOfYearOfEra).property]; omega)
         := by
  simp [month_from_shifted_month] at hm
  have h : mp.toNat = 11 := by omega
  have h1 : 11 < (monthSizes leapOfYearOfEra).val.size :=
    (isSome_getElem? (monthSizes leapOfYearOfEra).val 11).mp rfl
  have h2 : mp.toNat < (monthSizes leapOfYearOfEra).val.size := lt_of_eq_of_lt h h1
  rw [Array.get_eq_get_of_eq (monthSizes leapOfYearOfEra).val mp.toNat 11 h2 h1 h]
  have h1 : (monthSizes leapOfYearOfEra).val[11]'h1 = if leapOfYearOfEra then 29 else 28 := rfl
  have h2 : (Month.Ordinal.days leapOfYear ⟨2, m_le hmp hm⟩).val = if leapOfYear then 29 else 28 := by
    cases leapOfYear <;> rfl
  rw [h1, h2]

  rw [hIsLeap (by omega)]
  cases leapOfYear <;> simp

theorem days_eq_days_of_monthSizes (leapOfYear leapOfYearOfEra : Bool) (month : Month.Ordinal)
  (mp : Int) (hm : month.val = month_from_shifted_month mp)
  (hmp' : 0 ≤ mp ∧ mp ≤ 11) (hIsLeap : 10 ≤ mp → leapOfYearOfEra = leapOfYear)
    : Month.Ordinal.days leapOfYear month
    = ⟨(monthSizes leapOfYearOfEra).val[mp.toNat]'
          (by rw [(monthSizes leapOfYearOfEra).property]; omega),
        by
          have := monthSizesLeap_le leapOfYearOfEra mp.toNat (by omega)
          exact And.intro (by omega) (by norm_cast; simp_all)⟩ := by

  match month with
  | ⟨m, hm'⟩ =>
    if h' : m = 2
    then
      simp at hm
      rw [h'] at hm

      rw [Subtype.ext_iff]
      simp [Subtype.val]
      have h := days_eq_days_of_mp_2 leapOfYear leapOfYearOfEra mp hm hmp' hIsLeap
      have : (⟨m, hm'⟩ : Month.Ordinal)= Month.Ordinal.ofNat 2 := by
        rw [Subtype.ext_iff]
        simp
        rw [h']
        exact rfl
      rw [this]
      exact h
    else
      have := ordinalMonthSizes_eq_days leapOfYear ⟨m, hm'⟩
      rw [← this]
      have hx := to_index_from_shifted_eq leapOfYear mp ⟨m, hm'⟩ hmp' hm
      rw [hx]

      match mp with
      | Int.ofNat mp =>
        have : mp ≤ 11 := Int.ofNat_le.mp hmp'.right
        have h : mp < 11 := by
          simp [month_from_shifted_month] at hm
          omega
        have h := monthSizes_eq_ordinalMonthSizes leapOfYear leapOfYearOfEra ⟨mp, by
          have := (monthSizes leapOfYearOfEra).property
          omega⟩ h
        simp
        simp at h
        rw [Subtype.ext_iff]
        simp
        exact id (Eq.symm h)
      | Int.negSucc _ =>
        omega

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
    | Int.ofNat day =>
        rename_i heq' h'
        have hlt : n * 153 ≤ m' ∧ m' < (n+1) * 153 := by
          have h : n = m' / n' := Int.ofNat_inj.mp h'
          simp [← Int.ofNat.inj heq'] at h
          omega
        simp
        have heq : 5 * day + 2 = m' := Int.ofNat.inj heq
        rw [← heq] at hlt
        exact And.intro
          (doy_from_month_le n m' day heq (by omega))
          (doy_from_next_month_le n m' day heq (by omega))
    | Int.negSucc _ => contradiction
  · contradiction
  · omega
  · contradiction

theorem doy_sub_le (mp doy : Int) (leap : Bool) (hmp : mp = month_from_doy doy)
  (hmp' : 0 ≤ mp ∧ mp ≤ 11) (hdoy : 0 ≤ doy ∧ doy ≤ (if leap then 365 else 364))
    : doy - doy_from_month mp + 1 ≤ (monthSizes leap).val[mp.toNat]'
        (by rw [(monthSizes leap).property]; omega) := by
  have hlt := month_from_doy_le mp.toNat doy (by omega) hdoy.left
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

theorem mod_4_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 4 = 0 ↔ (yoe + 1 + era * 400).tmod 4 = 0  := by
  have : 4 * (era * 100) = era * 400 := by omega
  rw [← this]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 4 = 0 := by exact Int.natAbs_eq_zero.mp h
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*100) 4).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*100) 4).mpr h
      exact Int.ofNat_eq_zero.mp this)

theorem mod_100_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 100 = 0 ↔ (yoe + 1 + era * 400).tmod 100 = 0  := by
  have : 100 * (era * 4) = era * 400 := by omega
  rw [← this]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 100 = 0 := Int.natAbs_eq_zero.mp h
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*4) 100).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) (era*4) 100).mpr h
      exact Int.ofNat_eq_zero.mp this)

theorem mod_400_zero_of_add_iff (era : Int) (yoe : Nat)
    : (yoe + 1) % 400 = 0 ↔ (yoe + 1 + era * 400).tmod 400 = 0  := by
  rw [Int.mul_comm]
  exact Iff.intro
    (fun h => by
      have h : ((yoe:Int) + 1).tmod 400 = 0 := Int.natAbs_eq_zero.mp h
      exact (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) era 400).mp h)
    (fun h => by
      have := (Int.mod_zero_of_add_mul_eq_iff (yoe + 1) era 400).mpr h
      exact Int.ofNat_eq_zero.mp this)

/-- Is leap year of year defined by  `era` and `yoe` starting at 0
-/
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
  have hy : y = y' + 1 := by omega
  have heq : (Year.Offset.ofInt y).toInt = y := rfl
  have hmax : max yoe 0 = yoe := by omega
  rw [isLeapOfYearOfEras_eq era yoe]

  simp [isLeapOfYearOfEras, Year.Offset.isLeap]
  rw [heq, hy, hy', hmax]

private theorem m_to_mp (m mp y y' : Int) (hm : y = y' + (if m <= 2 then 1 else 0))
  (hle : 0 ≤ mp ∧ mp ≤ 11) (hmp : m = month_from_shifted_month mp)
    : y = y' + if 10 ≤ mp then 1 else 0 := by
  simp [month_from_shifted_month] at hmp
  omega

/--
Proof that the date `(year, month, day)` of `ofDaysSinceUNIXEpoch'` is valid.
-/
theorem isValid (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal)
  {era yoe doy y' mp : Int}
  (hyoe : 0 ≤ yoe ∧ yoe ≤ 399 )
  (hdoy : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364))
  (hmp' : 0 ≤ mp ∧ mp ≤ 11)
  (hmp : mp = month_from_doy doy)
  (hy' : y' = yoe + era * 400)
  (hm : month.val = month_from_shifted_month mp)
  (hd : day.val = doy - (doy_from_month mp) + 1)
  (hy : year.toInt = y' + (if month.val <= 2 then 1 else 0))
    : day ≤ month.days year.isLeap := by
  have hIsLeap : 10 ≤ mp → isLeapOfYearOfEra yoe.toNat = year.isLeap :=
    is_leap_of_year_of_era_eq_is_leap_of_year era yoe mp y' year hyoe
          hy' (m_to_mp month.val mp year y' hy hmp' hm)
  rw [days_eq_days_of_monthSizes year.isLeap (isLeapOfYearOfEra yoe.toNat) month mp hm hmp' hIsLeap]
  have hp := day.property
  have : day = ⟨doy - (doy_from_month mp) + 1, And.intro (by omega) (by omega)⟩ := by
    rw [Subtype.ext_iff]
    exact hd
  rw [this]
  exact doy_sub_le mp doy (isLeapOfYearOfEra yoe.toNat) hmp hmp' (by split at hdoy <;> simp_all)

end Verification


open Verification in

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
  let yoe := yoe_from_doe doe
  have hyoe : 0 ≤ yoe ∧ yoe ≤ 399 := yoe_le hdoe rfl
  let y' := yoe + era * 400
  let doy := doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100)
  have hdoy : 0 ≤ doy ∧ (if isLeapOfYearOfEra yoe.toNat then doy ≤ 365 else doy ≤ 364) :=
    doy_le hdoe hyoe rfl rfl
  let mp := month_from_doy doy
  have hmp : 0 ≤ mp ∧ mp ≤ 11 := mp_le (day_le_of hdoy) rfl
  let d := doy - (doy_from_month mp) + 1
  have hd : 1 ≤ d ∧ d ≤ 31 := d_le (day_le_of hdoy) hmp rfl rfl
  let m := month_from_shifted_month mp
  have hm : 1 ≤ m ∧ m ≤ 12 := m_le hmp rfl
  let y := y' + (if m <= 2 then 1 else 0)
  ⟨y, ⟨m, hm⟩, ⟨d, hd⟩, isValid y ⟨m, hm⟩ ⟨d, hd⟩ hyoe hdoy hmp rfl rfl rfl rfl rfl⟩

example : PlainDate.ofDaysSinceUNIXEpoch (-719468) =  ⟨0, 3, 1, by decide⟩ := rfl
example : ofDaysSinceUNIXEpoch' (-719468) =  ⟨0, 3, 1, by decide⟩ := rfl
