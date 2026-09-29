import ForestUnimodality.BridgeFlowData.Stage80.Cell192Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell192Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=6 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (48791411758721367202923539126581634123/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (763213344661497312338106823290316638893/500000000000000000000000000000000000000)

def table : Table :=
  ⟨6, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-6931471805599453/10000000000000000), 64, (12500000000000000117715401518227207655220381863401/25000000000000000000000000000000000000000000000000), (10000000000000000094172321214581766124176305490721/20000000000000000000000000000000000000000000000000)⟩, (156250000000000002942885037955680205237425301182473385048512742973658232003260311235026097023286801/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (100000000000000001883446424291635331351952192756786966431048155503178937410572431896866372617099841/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell192Term02
