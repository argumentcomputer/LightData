import LSpec
import LightData

def data : List LightData := [
  .atom default, .cell default,
  true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\"",
  .atom ⟨#[1, 2, 3]⟩, .cell #[.atom ⟨#[1, 2, 3]⟩],
  (none : Option Nat), some 3, some (some 2), ("ars", 3, some #[3]),
  (.left 1 : Either Nat String), (.right #[3] : Either Nat (Array Nat)),
  .cell #[true, false, 0, 1, 255, 256, 300, 300000, "", "aaa", "\\", "\""],
  .cell #[.cell #[false, .cell #[true, 1, "hello", "world"]]]
]

open LSpec

def main := lspecIO $
  data.foldl (init := .done) fun tSeq d =>
  let bytes := d.toByteArray
  tSeq ++ withExceptOk s!"{d} deserializes" (LightData.ofByteArray bytes)
    fun d' => test s!"{d} roundtrips" (d == d')
