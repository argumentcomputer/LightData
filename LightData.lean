import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector
import YatimaStdLib.DataClasses
import YatimaStdLib.Either

inductive LightData
  | atom : ByteArray → LightData
  | cell : Array LightData → LightData
  deriving Inhabited, Ord

namespace LightData

partial def beq : LightData → LightData → Bool
  | atom x, atom y => x.beq y
  | cell x, cell y =>
    let rec aux : List LightData → List LightData → Bool
      | _ :: _, []
      | [], _ :: _ => false
      | [], [] => true
      | x :: xs, y :: ys => x.beq y && aux xs ys
    aux x.data y.data
  | _, _ => false

instance : BEq LightData := ⟨beq⟩

partial def toString : LightData → String
  | atom x => ToString.toString x
  | cell x => s!"({", ".intercalate $ x.data.map toString})"

instance : ToString LightData := ⟨toString⟩

section Encoding

def ofNat (x : Nat) : LightData := atom x.toByteArrayLE

instance : Encodable LightData LightData ε := ⟨id, pure⟩

instance : Encodable Bool LightData String where
  encode
  | Bool.true => ofNat 1
  | Bool.false => ofNat 0
  decode 
  | atom x => match x.asLEtoNat with
    | 0 => pure Bool.false
    | 1 => pure Bool.true
    | _ => throw s!"Expected a boolean but got {x}"
  | x => throw s!"Expected a boolean but got {x}" 

instance : Encodable Nat LightData String where
  encode := ofNat
  decode
    | atom bs => pure bs.asLEtoNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : Encodable String LightData String where
  encode (s: String) := .atom s.toUTF8
  decode
    | atom x => pure (String.fromUTF8Unchecked x)
    | x => throw s!"Expected a string but got {x}"

instance : Encodable ByteArray LightData String where
  encode := atom
  decode | atom x => pure x | x => throw s!"Expected a atome cellay but got {x}"

variable
  [hα : Encodable α LightData String]
  [hβ : Encodable β LightData String]

instance : Encodable (Array α) LightData String where
  encode x := cell $ x.map hα.encode
  decode
    | cell x => x.mapM hα.decode
    | x => throw s!"Expected an cellay but got {x}"

instance : Encodable (List α) LightData String where
  encode x := cell $ .mk $ x.map hα.encode
  decode
    | cell x => x.data.mapM hα.decode
    | x => throw s!"Expected a list but got {x}"

instance : Encodable (Option α) LightData String where
  encode | none => cell #[] | some a => cell $ #[hα.encode a]
  decode
    | cell #[] => pure none
    | cell $ #[x] => return some (← hα.decode x)
    | x => throw s!"Expected an option but got {x}"

instance : Encodable (α × β) LightData String where
  encode | (a, b) => cell #[hα.encode a, hβ.encode b]
  decode
    | cell #[a, b] => return (← hα.decode a, ← hβ.decode b)
    | x => throw s!"Expected a product but got {x}"

instance : Encodable (Either α β) LightData String where
  encode
    | .left  x => cell #[false, hα.encode x]
    | .right x => cell #[true, hβ.encode x]
  decode
    | cell #[b, x] => do
      let b : Bool ← Encodable.decode b
      if b then return .right (← hβ.decode x)
      else return .left (← hα.decode x)
    | x => throw s!"Expected an either but got {x}"

instance : OfNat LightData n := ⟨.ofNat n⟩

end Encoding

section SerDe

def countBytesCore : Nat → Nat → UInt8 → UInt8
  | 0, _, x => x
  | fuel + 1, n, x =>
    let n' := n / 256
    if n' = 0 then x
    else countBytesCore fuel n' (x+1)

def countBytes (n: Nat) : UInt8 := 
  (countBytesCore (n + 1) n 0)


def uInt8Core : Nat → UInt8 → UInt8
| 0, x => x
| fuel + 1, x => uInt8Core fuel (x+1)

def toUInt8 (x: Nat): UInt8 := uInt8Core x 0

/--
tag format: 0bXYSSSSSS
The tag stores 1 ctor_bit X indicating if the LightData is an cellay or a ByteArray
The tag stores 1 small_bit Y indicating if the LightData size is small (<= 64 bytes)
The tag stores 6 size_bits. If small_bit is set, these size_bits describe the
data_size, if small_bit is not set, these size_bits describe how many bytes are needed for the data_size
-/
def tag : LightData -> UInt8
| atom x => 
  let ctor_bit: UInt8 := 0b00000000 
  let size_bits : UInt8 := if x.size <= 64 then
    toUInt8 (0b01000000 + (Nat.land 0b00111111 x.size))
    else countBytes x.size
  ctor_bit + size_bits
| cell x =>
  let ctor_bit: UInt8 := 0b10000000 
  let size_bits : UInt8 := if x.size <= 64 then
    toUInt8 (0b01000000 + (Nat.land 0b00111111 x.size))
    else countBytes x.size
  ctor_bit + size_bits

partial def toByteArray : LightData -> ByteArray
| d@(atom x) => if x.size <= 64 
  then .mk #[d.tag] ++  x
  else .mk #[d.tag] ++ x.size.toByteArrayLE ++ x
| d@(cell x) => if x.size <= 64 
  then x.foldl (·.append ·.toByteArray) ⟨#[d.tag]⟩
  else x.foldl (·.append ·.toByteArray) ⟨#[d.tag]⟩ ++ x.size.toByteArrayLE


structure Bytes where
  bytes : ByteArray
  size  : Nat
  valid : bytes.size = size

abbrev OfBytesM := ReaderT Bytes $ ExceptT String $ StateM Nat

def readUInt8 : OfBytesM UInt8 := do
  let idx ← get
  let ctx ← read
  if h : idx < ctx.size then
    set idx.succ
    return ctx.bytes.get ⟨idx, by rw [ctx.valid]; exact h⟩
  else throw "No more bytes to read"

def readTag : OfBytesM (Bool × Bool × Nat) := do
  let x ← readUInt8
  let ctor_bit : Bool := Nat.land x.val 0b10000000 == 0b10000000
  let small_bit : Bool := (Nat.land x.val 0b01000000) == 0b01000000
  let size := (Nat.land x.val 0b00111111)
  let size := if small_bit && size == 0 then 64 else size
  return (ctor_bit, small_bit, size)

def readByteVector (n : Nat) : OfBytesM $ ByteVector n := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ⟨ctx.bytes.slice idx n, ByteArray.slice_size⟩
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

partial def readLightData : OfBytesM LightData := do
  match ← readTag with
  | (.false, .true, size) => return atom (← readByteVector size).1
  | (.false, .false, x) => do
    let size := (← readByteVector x).data.asLEtoNat
    return atom (← readByteVector size).1
  | (.true, .true, size) => 
    return cell $ ← List.range size |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)
  | (.true, .false, x) => do
    let size := (← readByteVector x).data.asLEtoNat
    return cell $ ← List.range size |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, rfl⟩) 0).1

def roundtrip [Encodable α LightData String] (x: α) : Except String α := do
  ofByteArray (toByteArray (Encodable.encode x)) >>= Encodable.decode

instance : Encodable LightData ByteArray String where
  encode := toByteArray
  decode := ofByteArray

end SerDe

end LightData
