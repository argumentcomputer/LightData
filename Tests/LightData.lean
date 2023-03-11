import LSpec
import LightData

open LSpec

def randUInt8 : IO UInt8 :=
  return .ofNat $ ← IO.rand 0 UInt8.size.pred

def randByteArray (maxSize : Nat) : IO ByteArray := do
  List.range (← IO.rand 0 maxSize) |>.foldlM (init := default) fun acc _ => do
    pure $ acc.push (← randUInt8)

def randLightData (maxWidth maxDepth : Nat) : IO LightData :=
  match maxDepth with
  | 0 => return .atom (← randByteArray maxWidth)
  | maxDepth + 1 => do
    if (← IO.rand 0 1) == 0 then -- atom
      return .atom (← randByteArray maxWidth)
    else -- cell
      let lds ← List.range (← IO.rand 0 maxWidth) |>.foldlM (init := #[])
        fun acc _ => do pure $ acc.push (← randLightData maxWidth maxDepth)
      return .cell lds

def MAXWIDTH := 66
def MAXDEPTH := 4
def NTESTS   := 100
def SEED     := 42

def mkRoundtripTests : IO TestSeq := do
  IO.setRandSeed SEED
  let lds ← List.range NTESTS |>.mapM fun _ => randLightData MAXWIDTH MAXDEPTH
  return lds.foldl (init := .done) fun tSeq (ld : LightData) =>
    match LightData.ofByteArray ld.toByteArray with
    | .ok ld' => if ld == ld' then tSeq else test s!"{ld} doesn't roundtrip" false
    | .error e => test s!"Deserialization error: {e}\nLightData:\n{ld}" false

variable [Encodable α LightData] [BEq α] [ToString α]

def mkEncodableRoundtripTests (as : List α) : TestSeq :=
  as.foldl (init := .done) fun tSeq a =>
    tSeq ++ withExceptOk s!"{a} deserializes" (LightData.roundtrip a)
      fun a' => test s!"{a} roundtrips" (a == a')

def main := do
  let roundtripTests ← mkRoundtripTests
  lspecIO $
    roundtripTests ++
    mkEncodableRoundtripTests [false, true] ++
    mkEncodableRoundtripTests [0, 1, UInt64.size, UInt64.size.succ] ++
    mkEncodableRoundtripTests ["", "aaa", "\\", "\""] ++
    mkEncodableRoundtripTests [#[0, 1, 2, 3], #[]] ++
    mkEncodableRoundtripTests [#[#[1, 2, 3]], #[#[]]] ++
    mkEncodableRoundtripTests [none, some 2] ++
    mkEncodableRoundtripTests [none, some #["hi", "bye"]] ++
    mkEncodableRoundtripTests (List.range 66) ++
    mkEncodableRoundtripTests (List.range 256)
    
