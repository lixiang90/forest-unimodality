import ForestUnimodality.BridgeFlowData.Stage80.Cell184Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell184Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=10 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2640015164696538225718211042969732127/1250000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (4083831339877401688010976782134344751751/2500000000000000000000000000000000000000)

def table : Table :=
  ⟨10, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-18716850867380597/20000000000000000), 64, (39225523421890899175261563517009363711144224240557/100000000000000000000000000000000000000000000000000), (19612761710945449587630781758504681855572112120279/50000000000000000000000000000000000000000000000000)⟩, (1538641687721311516171737788415541590323686389982186046234286664133229878387174341085618243403670249/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (384660421930327879042934447103885397580921597495566124320282611482895100378552089953260132963037841/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell184Term02
