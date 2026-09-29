import ForestUnimodality.BridgeFlowData.Stage80.Cell181Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell181Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=7 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (14530200146705139803062712286018763541/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (1680843720436663444752419993037540454113/1000000000000000000000000000000000000000)

def table : Table :=
  ⟨7, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-2518452445462237/3750000000000000), 64, (5108969774506928354035730259213984011284307607967/10000000000000000000000000000000000000000000000000), (51089697745069283540357302592139840112843076079671/100000000000000000000000000000000000000000000000000)⟩, (133352143216332452376717961991216824490682601843813349132436653698053381030573367267402030975286347197767936236261492313823752392349464060219300063/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (133352143216332452376717961991216824490682601843821179604083701310359269393566409737392788642724720990226546869714340330525442574543150973957090228711/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell181Term01
