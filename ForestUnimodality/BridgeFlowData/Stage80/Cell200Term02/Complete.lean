import ForestUnimodality.BridgeFlowData.Stage80.Cell200Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell200Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=11 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (50799236149609932516050523835220934633/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (820756150832341035963016567215329358227/500000000000000000000000000000000000000)

def table : Table :=
  ⟨11, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-3218875824868200749201518666452375279/4000000000000000000000000000000000000), 64, (8944271909999158785636694674925104941876966175367/20000000000000000000000000000000000000000000000000), (11180339887498948482045868343656381177346207719209/25000000000000000000000000000000000000000000000000)⟩, (80000000000000000000000000000000000002048108341481007073361684305943822756328838049431823797584689/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (125000000000000000000000000000000000003200169283569663722071381202278245990935637642825897787585681/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell200Term02
