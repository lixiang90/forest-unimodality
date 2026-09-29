import ForestUnimodality.BridgeFlowData.Stage99.Cell142Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell142Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=13 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (64693965045080194059775820710866062937/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (7590724100302714469799373912082431828501/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨13, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-3667364316359827/4000000000000000), 64, (19988996083948987825523527939606666292702709537261/50000000000000000000000000000000000000000000000000), (39977992167897975651047055879213332585405419074523/100000000000000000000000000000000000000000000000000)⟩, (399559964444127970744309552711269300077787389552368059717197030212867439713298134106181568747382121/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1598239857776511882977238210845077200311149558209552194853123916802771852964950963089897085827677529/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell142Term02
