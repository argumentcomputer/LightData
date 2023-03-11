import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector
import YatimaStdLib.Encodable
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

section EncodableInstances

instance : Encodable LightData LightData := ⟨id, pure⟩

def ofNat (x : Nat) : LightData := atom x.toByteArrayLE

instance : OfNat LightData n := ⟨.ofNat n⟩

instance : Encodable Bool LightData where
  encode
    | false => atom default
    | true  => cell default
  decode
    | atom ⟨#[]⟩ => pure false
    | cell #[]   => pure true
    | x => throw s!"Expected a boolean but got {x}"

instance : Encodable Nat LightData where
  encode := ofNat
  decode
    | atom bs => pure bs.asLEtoNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : Encodable String LightData where
  encode s := atom s.toUTF8
  decode
    | atom x => return String.fromUTF8Unchecked x
    | x => throw s!"Expected a string but got {x}"

instance : Encodable ByteArray LightData where
  encode := atom
  decode | atom x => pure x | x => throw s!"Expected a atome cellay but got {x}"

variable
  [hα : Encodable α LightData]
  [hβ : Encodable β LightData]

instance : Encodable (Array α) LightData where
  encode x := cell $ x.map hα.encode
  decode
    | cell x => x.mapM hα.decode
    | x => throw s!"Expected an cellay but got {x}"

instance : Encodable (List α) LightData where
  encode x := cell $ .mk $ x.map hα.encode
  decode
    | cell x => x.data.mapM hα.decode
    | x => throw s!"Expected a list but got {x}"

instance : Encodable (Option α) LightData where
  encode | none => atom ⟨#[]⟩ | some a => cell $ #[hα.encode a]
  decode
    | atom ⟨#[]⟩ => pure none
    | cell $ #[x] => return some (← hα.decode x)
    | x => throw s!"Expected an option but got {x}"

instance : Encodable (α × β) LightData where
  encode | (a, b) => cell #[hα.encode a, hβ.encode b]
  decode
    | cell #[a, b] => return (← hα.decode a, ← hβ.decode b)
    | x => throw s!"Expected a product but got {x}"

instance : Encodable (Either α β) LightData where
  encode
    | .left  x => cell #[false, hα.encode x]
    | .right x => cell #[true,  hβ.encode x]
  decode
    | cell #[false, x] => return .left (← hα.decode x)
    | cell #[true,  x] => return .right (← hβ.decode x)
    | x => throw s!"Expected an either but got {x}"

end EncodableInstances

section SerDe

def countBytes (n : Nat) : UInt8 :=
  if n == 0 then 1
  else .ofNat $ n.log2 / 8 + 1

/--
tag format: 0bXYSSSSSS
* The tag stores 1 ctorBit X indicating if the LightData is an cellay or a ByteArray
* The tag stores 1 smallBit Y indicating if the LightData size is small (<= 64 bytes)
* The tag stores 6 sizeBits. If smallBit is set, these sizeBits describe the
  dataSize, if smallBit is not set, these sizeBits describe how many bytes are
  needed for the dataSize
-/
def tag : LightData → UInt8
  | atom x =>
    if x.isEmpty then 0b00000000 else
    let size := x.size
    if size < 64 then 0b01000000 + UInt8.ofNat size else
    if size == 64 then 0b01000000 else
    countBytes size
  | cell x =>
    if x.isEmpty then 0b10000000 else
    let size := x.size
    if size < 64 then 0b11000000 + UInt8.ofNat size else
    if size == 64 then 0b11000000 else
    0b10000000 + countBytes size

partial def toByteArray : LightData → ByteArray
  | d@(atom x) => if x.size <= 64
    then .mk #[d.tag] ++ x
    else .mk #[d.tag] ++ x.size.toByteArrayLE ++ x
  | d@(cell x) => if x.size <= 64
    then Array.foldl (·.append ·.toByteArray) ⟨#[d.tag]⟩ x
    else Array.foldl (·.append ·.toByteArray) (⟨#[d.tag]⟩ ++ x.size.toByteArrayLE) x

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
  let ctorBit : Bool := x.land 0b10000000 == 0b10000000
  let smallBit : Bool := x.land 0b01000000 == 0b01000000
  let size := x.land 0b00111111
  let size := if smallBit && size == 0 then (64 : Nat) else size.val
  return (ctorBit, smallBit, size)

def readByteVector (n : Nat) : OfBytesM $ ByteVector n := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ⟨ctx.bytes.slice idx n, ByteArray.slice_size⟩
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

partial def readLightData : OfBytesM LightData := do
  match ← readTag with
  | (false, true, size) => return atom (← readByteVector size).1
  | (false, false, x) => do
    let size := (← readByteVector x).data.asLEtoNat
    return atom (← readByteVector size).1
  | (true, true, size) =>
    return cell $ ← List.range size |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)
  | (true, false, x) => do
    let size := (← readByteVector x).data.asLEtoNat
    return cell $ ← List.range size |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, rfl⟩) 0).1

def roundtrip [Encodable α LightData] (x: α) : Except String α := do
  ofByteArray (toByteArray (Encodable.encode x)) >>= Encodable.decode

instance : Encodable LightData ByteArray where
  encode := toByteArray
  decode := ofByteArray

end SerDe

end LightData
