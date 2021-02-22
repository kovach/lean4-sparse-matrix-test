import Tensor.Basic

open SparseVec

section ParsingMtx
open DenseVec
open SparseVec

def parseFloat! : String → Float
| str => do
    let mut (sign, digits) : (Bool × String) := if str.front == '-' then (true, str.drop 1) else (false, str)
    let pred c := c.isDigit
    let (int, digits) := (Float.ofScientific (digits.takeWhile pred).toNat! false 0, digits.dropWhile pred)
    let fracStr := String.takeWhile (digits.drop 1) pred
    let frac := Float.ofScientific (fracStr.toNat!) true fracStr.length
    if sign then 0.0 - (int + frac) else int + frac

#eval parseFloat! "-3.534"

def parseMTX (input : String) : (Nat × Nat × SparseVec Nat (SparseVec Nat Float)) := do
    let ValueType := Float
    let mut result : SparseVec Nat (SparseVec Nat ValueType) := #[]
    let mut currentRowIndex : Nat := 1 -- TODO read from first line
    let mut currentRow : SparseVec Nat ValueType := #[]
    let mut nnz := 0

    let lines := List.dropWhile (λ line => line.front == '%') (input.splitOn "\n")
    for line in lines.drop 1 do {
        nnz := nnz + 1
        let data := line.splitOn " "
        match data with
        | [col, row, value] =>
            let rowN := row.toNat!
            if  rowN != currentRowIndex then
                result := result.push (currentRowIndex, currentRow)
                currentRowIndex := rowN
                currentRow := #[]
            currentRow := currentRow.push (col.toNat!, parseFloat! value)
        | _ => () -- issue? return ()  no good
    }
    result := result.push (currentRowIndex, currentRow)
    let n := currentRowIndex
    -- result := result[:10000]
    return (n, nnz, SparseVec.sparseTranspose n result)

def loadTestCase : IO (Nat × SparseVec Nat (SparseVec Nat Float)) := do
    let bench_too_large := "../../taco/benchmarks/thermomech_dK/thermomech_dK.mtx"
    let benchSmall := "../../taco/benchmarks/sherman2/sherman2.mtx"
    let benchTiny := "../../taco/benchmarks/test.mtx"
    let input ← IO.FS.readFile benchSmall
    let (n, nnz, matrix) := parseMTX input
    IO.println s!"rows: {n}"
    IO.println s!"nnz:  {nnz}"
    return (n, matrix)
end ParsingMtx

def printResult (out : Matrix) : IO Unit := do
    IO.println "printing result"
    IO.println s!"num nonzero rows: {out.size}"

    for (index, row) in out[0:2] do
        IO.println s!"{index}: {row[0:3].toArray}"

    IO.println "done"

def main : IO UInt32 := do
    let (n, A) ← loadTestCase
    let A' := sparseTranspose n A
    IO.println "computing"

    let out := A' * A
    printResult out

    IO.println "updated"

    return 0