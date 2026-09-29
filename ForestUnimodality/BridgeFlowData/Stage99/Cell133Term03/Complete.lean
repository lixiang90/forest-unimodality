import ForestUnimodality.BridgeFlowData.Stage99.Cell133Term03.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell133Term03
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=12 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2658980444838863205353611645121577837/500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (4149872017259468373352883479646946878337/2500000000000000000000000000000000000000)

def table : Table :=
  ⟨12, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-2285440939468121/3000000000000000), 64, (1867276056489411801071502336128490124618986097187/4000000000000000000000000000000000000000000000000), (11670475353058823756696889600803063278868663107419/25000000000000000000000000000000000000000000000000)⟩, (6510668531063046607456300073071514548329309594057914387638313027091139622647219337414981918701323237435250139446531325913805863298822249933518203/64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1589518684341564113148510760027225231525710350111897654790734781487433564908698948738232093249753365757630375292453100052049407727949527199650641059/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell133Term03
