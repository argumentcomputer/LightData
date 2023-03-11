import LSpec
import LightData

open LSpec

variable [Encodable α LightData] [BEq α] [ToString α]

def mkRoundtripTests (as : List α) : TestSeq :=
  as.foldl (init := .done) fun tSeq a =>
    tSeq ++ withExceptOk s!"{a} deserializes" (LightData.roundtrip a)
      fun a' => test s!"{a} roundtrips" (a == a')

def main := lspecIO $
  mkRoundtripTests [false, true] ++
  mkRoundtripTests [0, 1, UInt64.size, UInt64.size.succ] ++
  mkRoundtripTests ["", "aaa", "\\", "\""] ++
  mkRoundtripTests [#[0, 1, 2, 3], #[]] ++
  mkRoundtripTests [#[#[1, 2, 3]], #[#[]]] ++
  mkRoundtripTests [none, some 2] ++
  mkRoundtripTests [none, some #["hi", "bye"]] ++
  mkRoundtripTests (List.range 66) ++
  mkRoundtripTests (List.range 256)
