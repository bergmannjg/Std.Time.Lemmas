# Std.Time.PlainDate.ofDaysSinceUNIXEpoch is a valid date

Proof that *Std.Time.PlainDate.ofDaysSinceUNIXEpoch* gives a valid *Std.Time.PlainDate*.

## [ofDaysSinceUNIXEpoch](https://github.com/leanprover/lean4/blob/v4.20.0/src/Std/Time/Date/PlainDate.lean#L94) with clipping the day

```lean
def ofDaysSinceUNIXEpoch (day : Day.Offset) : PlainDate :=
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
  let doe := z - era * 146097
  let yoe := (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100)
  let mp := (5 * doy + 2).tdiv 153
  let d := doy - (153 * mp + 2).tdiv 5 + 1
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)
  .ofYearMonthDayClip y (.clip m (by decide)) (.clip d (by decide))
```

## [ofDaysSinceUNIXEpoch](https://github.com/bergmannjg/Std.Time.Lemmas/blob/main/Time/Date/Lemmas.lean#L847) with proof that date is valid

```lean
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
```
