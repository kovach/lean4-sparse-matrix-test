-- Scott Kovach
import Tensor.Basic

open SparseVec

section ParsingMtx

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
        | _ => () -- issue? return () no good
    }
    result := result.push (currentRowIndex, currentRow)
    let n := currentRowIndex
    return (n, nnz, SparseVec.sparseTranspose result)

def loadTestCase : IO (Nat × SparseVec Nat (SparseVec Nat Float)) := do
    let benchmarkFile := "sherman2.mtx"
    let input ← IO.FS.readFile benchmarkFile
    let (n, nnz, matrix) := parseMTX input
    IO.println s!"rows: {n}"
    IO.println s!"nnz:  {nnz}"
    return (n, matrix)

end ParsingMtx

def printTruncatedResult (m : Matrix) : IO Unit := do
    IO.println "printing result"
    IO.println s!"num nonzero rows: {m.size}"

    for (index, row) in m[0:2] do
        IO.println s!"{index}: {row[0:3].toArray}"

    IO.println "done"

/- expected output for Aᵀ * A
1: #[(1, 29219761447887.066406), (2, 4508680898504.898438), (3, -494715800453.345886)]
2: #[(1, 4508680898504.898438), (2, 695717389901.341919), (3, -76345788006.166794)]
-/
def main : IO UInt32 := do
    let (n, A) ← loadTestCase
    IO.println "computing"

    let out := Aᵀ * A -- linearCombinationOfRows (sparseTranspose A) A
    printTruncatedResult out

    IO.println "finished"
    return 0