import ForestUnimodality.BridgeFlowData.Stage80.Cell187Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell187Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=16 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (20871042606580646598026878578834187413/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (8185036901638256589581504808517490973043/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨16, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-940078678333151/1000000000000000), 64, (1220615945689277691482316604436175223030941320911/3125000000000000000000000000000000000000000000000), (39059710262056886127434131341957607136990122269153/100000000000000000000000000000000000000000000000000)⟩, (1489903286870929706987316401801298056197080145445853483090749427838226816585497341645717485869921/9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1525660965755832019955011995444529209545810068936632086105451527878599128446233193059488685775337409/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell187Term01
