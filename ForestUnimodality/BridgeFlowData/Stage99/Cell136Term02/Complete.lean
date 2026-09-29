import ForestUnimodality.BridgeFlowData.Stage99.Cell136Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell136Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=13 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (25983940666730914201281138595144454659/2000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (7576107282823257660469198299892249876519/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨13, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-9151744581635071/10000000000000000), 64, (2502792242440091304333552142524701412427859204793/6250000000000000000000000000000000000000000000000), (40044675879041460869336834280395222598845747276689/100000000000000000000000000000000000000000000000000)⟩, (6263969008818300768709030921376609187604413230243274682870296128814034035179232034558098314172849/39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1603576066257484996789511915872411952026729786942358408166553891898131386674444191292070859922802721/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell136Term02
