import ForestUnimodality.CoupledFlowData.Cell199Term00.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell199Term00
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=11 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (125624556226762898761476180845487712611/250000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (10891482256430523308360090374907811197153/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨11, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-5129329438755053342619614425468723841/100000000000000000000000000000000000000), 64, (4750000000000000000000000000000000000138806218027/5000000000000000000000000000000000000000000000000), (95000000000000000000000000000000000002776124360541/100000000000000000000000000000000000000000000000000)⟩, (4750000000000000000000000000000000000138806218027/5000000000000000000000000000000000000000000000000), (95000000000000000000000000000000000002776124360541/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.CoupledFlowData.Cell199Term00
