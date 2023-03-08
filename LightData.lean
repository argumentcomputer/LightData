import YatimaStdLib.ByteArray
import YatimaStdLib.ByteVector
import YatimaStdLib.DataClasses
import YatimaStdLib.Ord
import YatimaStdLib.Array
import YatimaStdLib.Either

inductive LightData
  | byt : ByteArray → LightData
  | arr : Array LightData → LightData
  deriving Inhabited, Ord

namespace LightData

partial def beq : LightData → LightData → Bool
  | byt x, byt y => x.beq y
  | arr x, arr y =>
    let rec aux : List LightData → List LightData → Bool
      | _ :: _, []
      | [], _ :: _ => false
      | [], [] => true
      | x :: xs, y :: ys => x.beq y && aux xs ys
    aux x.data y.data
  | _, _ => false

instance : BEq LightData := ⟨beq⟩

partial def toString : LightData → String
  | byt x => ToString.toString x
  | arr x => s!"({", ".intercalate $ x.data.map toString})"

instance : ToString LightData := ⟨toString⟩

section Encoding

def ofNat (x : Nat) : LightData := byt x.toByteArrayLE

instance : Encodable LightData LightData ε := ⟨id, pure⟩

instance : Encodable Bool LightData String where
  encode
  | Bool.true => ofNat 1
  | Bool.false => ofNat 0
  decode 
  | byt x => match x.asLEtoNat with
    | 0 => pure Bool.false
    | 1 => pure Bool.true
    | _ => throw s!"Expected a boolean but got {x}"
  | x => throw s!"Expected a boolean but got {x}" 

instance : Encodable Nat LightData String where
  encode := ofNat
  decode
    | byt bs => pure bs.asLEtoNat
    | x => throw s!"Expected a numeric value but got {x}"

instance : Encodable String LightData String where
  encode (s: String) := .byt s.toUTF8
  decode | byt x => pure (String.fromUTF8Unchecked x) | x => throw s!"Expected a string but got {x}"

instance : Encodable ByteArray LightData String where
  encode := byt
  decode | byt x => pure x | x => throw s!"Expected a byte array but got {x}"

instance [Encodable α LightData String] : Encodable (Array α) LightData String where
  encode x := arr $ x.map Encodable.encode
  decode
    | arr x => x.mapM Encodable.decode
    | x => throw s!"Expected an array but got {x}"

instance [Encodable α LightData String] : Encodable (List α) LightData String where
  encode x := arr $ .mk $ x.map Encodable.encode
  decode
    | arr x => x.data.mapM Encodable.decode
    | x => throw s!"Expected a list but got {x}"

instance [Encodable α LightData String] : Encodable (Option α) LightData String where
  encode | none => arr #[] | some a => arr $ #[ (Encodable.encode a) ]
  decode
    | arr #[] => pure none
    | arr $ #[ x ] => return some (← Encodable.decode x)
    | x => throw s!"Expected an option but got {x}"

instance [Encodable α LightData String] [Encodable β LightData String] : Encodable (α × β) LightData String where
  encode | (a, b) => arr #[Encodable.encode a, Encodable.encode b]
  decode
    | arr #[a, b] => return (← Encodable.decode a, ← Encodable.decode b)
    | x => throw s!"Expected a product but got {x}"

instance [Encodable α LightData String] [Encodable β LightData String]: Encodable (Either α β) LightData String where
  encode
    | .left x => arr #[(Encodable.encode Bool.false), (Encodable.encode x)]
    | .right x => arr #[(Encodable.encode Bool.true), (Encodable.encode x)]
  decode
    | arr #[b, x] => do
      let b : Bool ← Encodable.decode b
      if b then return (.right (← Encodable.decode x)) 
      else return (.left (← Encodable.decode x)) 
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

-- the tag stores 1 bit indicating if the LightData is an array or a ByteArray
-- and then seven bits of size_bytes indicating the number of bytes of size
-- immediately following the tag. The maximum value of size_bytes is 127, but in
-- practice, for a UInt64 size field, the value should be 8.
def tag : LightData → UInt8
  | byt x => 0b00000000 + countBytes x.size
  | arr x => 0b10000000 + countBytes x.size

partial def toByteArray (d : LightData) : ByteArray :=
  match d with
  | byt x => .mk #[d.tag] ++ (x.size.toByteArrayLE) ++ x
  | arr x => x.foldl (fun acc x => acc.append x.toByteArray) (⟨#[d.tag]⟩ ++ x.size.toByteArrayLE)

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

def readTag : OfBytesM (Nat × Nat) := do
  let x ← readUInt8
  return (Nat.land x.val 0b10000000, Nat.land x.val 0b1111111)

def readByteVector (n : Nat) : OfBytesM $ ByteVector n := do
  let idx ← get
  let ctx ← read
  if idx + n - 1 < ctx.size then
    set $ idx + n
    return ⟨ctx.bytes.slice idx n, ByteArray.slice_size⟩
  else throw s!"Not enough data to read {n} bytes (size {ctx.size}, idx {idx})"

partial def readLightData : OfBytesM LightData := do
  match ← readTag with
  | (0, x) => do
    let size ← readByteVector x
    let size := Nat.fromByteListBE size.data.data.data.reverse
    return byt (← readByteVector size).1
  | (1, x) => do
    let size ← readByteVector x
    let size := Nat.fromByteListBE size.data.data.data.reverse
    return arr $ ← List.range size |>.foldlM (init := #[])
      fun acc _ => do pure $ acc.push (← readLightData)
  | x => throw s!"Invalid LightData tag: {x}"

def ofByteArray (bytes : ByteArray) : Except String LightData :=
  (StateT.run (ReaderT.run readLightData ⟨bytes, bytes.size, rfl⟩) 0).1

instance : Encodable LightData ByteArray String where
  encode := toByteArray
  decode := ofByteArray

end SerDe

--section Hashing
--
--protected partial def hash (d : LightData) : ByteVector 32 :=
--  d.toByteArray.blake3
--
--instance : HashRepr LightData (ByteVector 32) where
--  hashFunc := LightData.hash
--  hashRepr := lnk
--
--end Hashing
--
end LightData
