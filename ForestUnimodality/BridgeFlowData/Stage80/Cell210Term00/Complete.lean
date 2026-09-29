import ForestUnimodality.BridgeFlowData.Stage80.Cell210Term00.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell210Term00
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=4 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (16277288633087916668222175520573883687/1250000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (16179676273490801557610938205747968438157/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨4, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-120397280432593599262274621776183850293/200000000000000000000000000000000000000), 64, (10954451150103322269139395656016042679184216294021/20000000000000000000000000000000000000000000000000), (27386127875258305672848489140040106697960540735053/50000000000000000000000000000000000000000000000000)⟩, (120000000000000000000000000000000000002833311696718610636848061825155300032329032687500831520348441/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (750000000000000000000000000000000000017708198104518702608175644712893473691196494403578157542912809/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.environment)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 environment rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell210Term00
